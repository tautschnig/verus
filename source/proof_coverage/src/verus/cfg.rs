//! Per-function control graphs, built from the SST tree
//! (`PROOF_COVERAGE.md` §3: `control_graphs`).
//!
//! The SST is the right substrate: it is the last IR where loops are loops
//! and calls are single statements (structured AIR has already dismantled
//! them, and the loop body may live in a different query). One recursive
//! walk produces the graph *and* every SST side-table the producer needs
//! (assume rows, loop records, call sites), so their orders are consistent
//! by construction.
//!
//! Node identity is the structural path through the SST tree (`b0.t.b2`…) —
//! deterministic, span-independent. Spans are display metadata on nodes.

use crate::record::{
    AssumeIntent as RecordAssumeIntent, LemmaRecord, LoopRecord, RecursiveCallRecord, SstAssume,
};
use std::sync::Arc;
use vir::sst::{AssumeIntent, Exp, FuncCheckSst, Stm, StmX};

/// Classifier for an assume's formula, supplied by the producer:
/// (will the AIR-side shape/positional rules recognize it?, op-skeleton sig).
pub type RecognizablePredicate<'p> = &'p dyn Fn(&AssumeIntent, &Exp) -> (bool, String);
pub type SigPredicate<'p> = &'p dyn Fn(&Exp) -> String;

fn record_assume_intent(intent: AssumeIntent) -> RecordAssumeIntent {
    match intent {
        AssumeIntent::UserAssume => RecordAssumeIntent::UserAssume,
        AssumeIntent::AssertedProposition => RecordAssumeIntent::AssertedProposition,
        AssumeIntent::CheckedCondition => RecordAssumeIntent::CheckedCondition,
        AssumeIntent::HasType => RecordAssumeIntent::HasType,
        AssumeIntent::HasResolved => RecordAssumeIntent::HasResolved,
        AssumeIntent::TypeInvariant => RecordAssumeIntent::TypeInvariant,
        AssumeIntent::PathTermination => RecordAssumeIntent::PathTermination,
        AssumeIntent::AssertForallRequire => RecordAssumeIntent::AssertForallRequire,
        AssumeIntent::AssertForallEnsures => RecordAssumeIntent::AssertForallEnsures,
        AssumeIntent::AssertQueryRequire => RecordAssumeIntent::AssertQueryRequire,
        AssumeIntent::AssertQueryEnsures => RecordAssumeIntent::AssertQueryEnsures,
        AssumeIntent::OpenedInvariant => RecordAssumeIntent::OpenedInvariant,
        AssumeIntent::AtomicUpdate => RecordAssumeIntent::AtomicUpdate,
        AssumeIntent::AtomicUpdateEnsures => RecordAssumeIntent::AtomicUpdateEnsures,
        AssumeIntent::ClosureSpec => RecordAssumeIntent::ClosureSpec,
        AssumeIntent::ClosureRequires => RecordAssumeIntent::ClosureRequires,
        AssumeIntent::FunctionRequires => RecordAssumeIntent::FunctionRequires,
        AssumeIntent::MutRefCurrent => RecordAssumeIntent::MutRefCurrent,
        AssumeIntent::VarEquality => RecordAssumeIntent::VarEquality,
        AssumeIntent::ExpandErrorsSplit => RecordAssumeIntent::ExpandErrorsSplit,
    }
}

pub use proof_coverage_core::record::{CfgEdge, CfgEdgeKind, CfgNode, CfgNodeKind, CfgRecord};

/// Everything the single walk produces.
pub struct SstInfo {
    pub cfg: CfgRecord,
    pub assumes: Vec<SstAssume>,
    pub lemmas: Vec<LemmaRecord>,
    pub recursive_calls: Vec<RecursiveCallRecord>,
    pub loops: Vec<LoopRecord>,
    /// Exact process-local source identities for each declaring loop clause.
    pub loop_source_ids: Vec<(u64, Vec<vir::messages::AstId>)>,
    pub call_sites: Vec<CallSite>,
    /// `if` statements: (branch node, condition expression span).
    pub branches: Vec<(String, String)>,
    /// CFG nodes for implicit function-tail returns. These are distinguished
    /// constructionally by SST's `inside_body` bit, so the source tail can be
    /// joined even when expression lowering replaces its span identity with
    /// an enclosing block's.
    pub implicit_return_nodes: Vec<String>,
    /// Assignment nodes binding compiler temporaries.
    pub synthetic_bindings: Vec<String>,
    /// Process-local statement identities for exact lowering-sidecar joins.
    /// These are resolved before serialization.
    pub sites: Vec<SstSite>,
    /// `(node, innermost enclosing invariant-block node)`.
    pub invariant_block_members: Vec<(String, String)>,
}

#[derive(Clone)]
pub struct SstSite {
    pub statement: usize,
    pub node: String,
    pub span: String,
    /// For a user-defined type invariant assumption: the invariant function
    /// the SST applies (`ExpX::Call(CallFun::Fun(inv), _, [value])`). The
    /// assumption's subject is that function; its site is the statement.
    pub subject_fn: Option<String>,
    /// VIR source identities carried by this structured site. The producer
    /// resolves these to stable source-artifact ids before serialization.
    pub source_ids: Vec<vir::messages::AstId>,
}

fn statement_source_ids(stm: &Stm) -> Vec<vir::messages::AstId> {
    let mut ids = vec![stm.span.id];
    match &stm.x {
        StmX::If(cond, ..) => ids.push(cond.span.id),
        StmX::Loop { cond, invs, decrease, .. } => {
            if let Some((_, cond)) = cond {
                ids.push(cond.span.id);
            }
            ids.extend(invs.iter().map(|inv| inv.inv.span.id));
            ids.extend(decrease.iter().map(|dec| dec.span.id));
        }
        _ => {}
    }
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// The type-invariant function a `TypeInvariant` assumption applies, if the
/// statement is one. SST elaboration hoists the call into a temporary
/// (`tmp%n = wf(x); assume(tmp%n)`), so the call is found either directly in
/// the assumed expression or through the temporary's defining assignment,
/// recorded in `temps` as the walk passes it.
fn type_invariant_subject(
    stm: &Stm,
    temps: &std::collections::HashMap<vir::ast::VarIdent, String>,
) -> Option<String> {
    use vir::sst::{CallFun, ExpX};
    match &stm.x {
        StmX::Assume(AssumeIntent::TypeInvariant, exp) => match &exp.x {
            ExpX::Call(CallFun::Fun(fun, _), _, _) => Some(super::fun_identity(fun)),
            ExpX::Var(ident) => temps.get(ident).cloned(),
            _ => None,
        },
        _ => None,
    }
}

/// If `stm` binds a temporary to a function call, record which function.
fn note_temp_call(stm: &Stm, temps: &mut std::collections::HashMap<vir::ast::VarIdent, String>) {
    use vir::sst::{CallFun, ExpX};
    if let StmX::Assign { lhs, rhs } = &stm.x {
        if let (ExpX::VarLoc(ident), ExpX::Call(CallFun::Fun(fun, _), _, _)) = (&lhs.dest.x, &rhs.x)
        {
            temps.insert(ident.clone(), super::fun_identity(fun));
        }
    }
}

/// Resolve process-local statement pointers in the exact post-transform SST
/// body to the same deterministic structural paths used by the CFG walk.
pub fn sites_for_body(body: &Stm) -> Vec<SstSite> {
    fn walk(
        stm: &Stm,
        path: &mut Vec<String>,
        out: &mut Vec<SstSite>,
        temps: &mut std::collections::HashMap<vir::ast::VarIdent, String>,
    ) {
        note_temp_call(stm, temps);
        out.push(SstSite {
            statement: Arc::as_ptr(stm) as usize,
            node: path.join("."),
            span: stm.span.as_string.clone(),
            subject_fn: type_invariant_subject(stm, temps),
            source_ids: statement_source_ids(stm),
        });
        match &stm.x {
            StmX::Block(stms) => {
                for (i, child) in stms.iter().enumerate() {
                    path.push(format!("b{}", i));
                    walk(child, path, out, temps);
                    path.pop();
                }
            }
            StmX::AssertQuery { body, .. } => {
                path.push("q".to_string());
                walk(body, path, out, temps);
                path.pop();
            }
            StmX::Call { body: Some(body), .. } => {
                path.push("cb".to_string());
                walk(body, path, out, temps);
                path.pop();
            }
            StmX::If(_, then_stm, else_stm) => {
                path.push("t".to_string());
                walk(then_stm, path, out, temps);
                path.pop();
                if let Some(else_stm) = else_stm {
                    path.push("e".to_string());
                    walk(else_stm, path, out, temps);
                    path.pop();
                }
            }
            StmX::Loop { pre_stms, cond, body, .. } => {
                for (i, child) in pre_stms.iter().enumerate() {
                    path.push(format!("p{}", i));
                    walk(child, path, out, temps);
                    path.pop();
                }
                if let Some((cond_stm, _)) = cond {
                    path.push("c".to_string());
                    walk(cond_stm, path, out, temps);
                    path.pop();
                }
                path.push("yb".to_string());
                walk(body, path, out, temps);
                path.pop();
            }
            StmX::DeadEnd(inner) => {
                path.push("d".to_string());
                walk(inner, path, out, temps);
                path.pop();
            }
            StmX::OpenInvariant(inner) => {
                path.push("o".to_string());
                walk(inner, path, out, temps);
                path.pop();
            }
            StmX::ClosureInner { body, .. } => {
                path.push("k".to_string());
                walk(body, path, out, temps);
                path.pop();
            }
            StmX::Call { body: None, .. }
            | StmX::AssertBitVector { .. }
            | StmX::Assert(..)
            | StmX::AssertCompute(..)
            | StmX::Assume(..)
            | StmX::Assign { .. }
            | StmX::Fuel(..)
            | StmX::RevealString(..)
            | StmX::RevealByteString(..)
            | StmX::Return { .. }
            | StmX::BreakOrContinue { .. }
            | StmX::Air(..) => {}
        }
    }

    let mut sites = Vec::new();
    walk(body, &mut vec!["r".to_string()], &mut sites, &mut std::collections::HashMap::new());
    sites
}

pub struct CallSite {
    pub node: String,
    pub span: String,
    /// Friendly callee name; None for AssumeExternal targets.
    pub callee: Option<String>,
    /// Friendly name of the statically resolved implementation, for a trait
    /// method call the verifier resolved (`CallTargetKind::DynamicResolved`).
    pub resolved_callee: Option<String>,
}

struct Walk<'p> {
    recognizable: RecognizablePredicate<'p>,
    sig_of: SigPredicate<'p>,
    /// True when `sst_to_air::Return` will emit the `assume_var` return
    /// binding: the postcondition has a return destination AND there is
    /// postcondition work (non-empty ens_exps; recommends mode differs and
    /// is not predicted). Gates the Return predicted row.
    return_binding_emitted: bool,
    nodes: Vec<CfgNode>,
    edges: Vec<CfgEdge>,
    /// Enclosing `OpenInvariant` statements, innermost last.
    invariant_blocks: Vec<String>,
    /// `(node, innermost enclosing invariant block)` for every node created
    /// inside a block.
    invariant_block_members: Vec<(String, String)>,
    assumes: Vec<SstAssume>,
    lemmas: Vec<LemmaRecord>,
    recursive_calls: Vec<RecursiveCallRecord>,
    /// Set by the Block arm for exactly one child: the guard node id of an
    /// Assert(CheckDecreaseHeight) whose *immediate sibling* is this call.
    /// Never survives past that child (block-local construction match).
    guard_for_next: Option<String>,
    lemma_span_stack: Vec<String>,
    /// AssertQueryEnsures spans seen since the last non-ensures assume;
    /// ast_to_sst emits a lemma's ensures assumes immediately *before* the
    /// AssertQuery region (observed SST walk order), so the buffer's content
    /// when a region closes is that region's ensures clause list.
    pending_ensures: Vec<String>,
    loops: Vec<LoopRecord>,
    loop_source_ids: Vec<(u64, Vec<vir::messages::AstId>)>,
    call_sites: Vec<CallSite>,
    branches: Vec<(String, String)>,
    implicit_return_nodes: Vec<String>,
    synthetic_bindings: Vec<String>,
    sites: Vec<SstSite>,
    /// Temporaries bound to function calls, for type-invariant subjects.
    temps: std::collections::HashMap<vir::ast::VarIdent, String>,
    /// Stack of (loop node id base, loop label) for break/continue targets.
    loop_stack: Vec<(String, Option<String>)>,
    /// Span of the innermost enclosing loop body, for assume attribution.
    loop_span_stack: Vec<String>,
    exit_id: String,
}

pub fn build(
    check: &FuncCheckSst,
    recognizable: RecognizablePredicate<'_>,
    sig_of: SigPredicate<'_>,
) -> SstInfo {
    let mut w = Walk {
        recognizable,
        sig_of,
        nodes: Vec::new(),
        edges: Vec::new(),
        invariant_blocks: Vec::new(),
        invariant_block_members: Vec::new(),
        assumes: Vec::new(),
        loops: Vec::new(),
        loop_source_ids: Vec::new(),
        call_sites: Vec::new(),
        branches: Vec::new(),
        implicit_return_nodes: Vec::new(),
        synthetic_bindings: Vec::new(),
        sites: Vec::new(),
        temps: std::collections::HashMap::new(),
        loop_stack: Vec::new(),
        loop_span_stack: Vec::new(),
        lemmas: Vec::new(),
        recursive_calls: Vec::new(),
        guard_for_next: None,
        lemma_span_stack: Vec::new(),
        pending_ensures: Vec::new(),
        return_binding_emitted: check.post_condition.dest.is_some()
            && !check.post_condition.ens_exps.is_empty(),
        exit_id: "exit".to_string(),
    };
    w.node("entry", CfgNodeKind::Entry, None);
    w.node("exit", CfgNodeKind::Exit, None);
    let last = w.walk(&check.body, "entry".to_string(), &mut vec!["r".to_string()]);
    w.edge(&last, "exit", CfgEdgeKind::Next);

    SstInfo {
        cfg: CfgRecord {
            entry: "entry".to_string(),
            exit: "exit".to_string(),
            nodes: w.nodes,
            edges: w.edges,
        },
        assumes: w.assumes,
        lemmas: w.lemmas,
        recursive_calls: w.recursive_calls,
        loops: w.loops,
        loop_source_ids: w.loop_source_ids,
        call_sites: w.call_sites,
        branches: w.branches,
        implicit_return_nodes: w.implicit_return_nodes,
        synthetic_bindings: w.synthetic_bindings,
        sites: w.sites,
        invariant_block_members: w.invariant_block_members,
    }
}

impl<'p> Walk<'p> {
    fn node(&mut self, id: &str, kind: CfgNodeKind, span: Option<&vir::messages::Span>) {
        self.nodes.push(CfgNode {
            id: id.to_string(),
            kind,
            span: span.map(|s| s.as_string.clone()),
        });
        // Membership in the enclosing invariant block, recorded where the walk
        // knows it. The open assumption and the close obligation of one block
        // are then paired by this relation instead of by comparing paths.
        if let Some(block) = self.invariant_blocks.last() {
            self.invariant_block_members.push((id.to_string(), block.clone()));
        }
    }

    fn edge(&mut self, from: &str, to: &str, kind: CfgEdgeKind) {
        self.edges.push(CfgEdge { from: from.to_string(), to: to.to_string(), kind });
    }

    /// Walk one statement; `pred` is the node control arrives from; returns
    /// the node control leaves through. `path` is the structural position.
    fn walk(&mut self, stm: &Stm, pred: String, path: &mut Vec<String>) -> String {
        let id = path.join(".");
        let span = &stm.span;
        note_temp_call(stm, &mut self.temps);
        self.sites.push(SstSite {
            statement: Arc::as_ptr(stm) as usize,
            node: id.clone(),
            span: span.as_string.clone(),
            subject_fn: type_invariant_subject(stm, &self.temps),
            source_ids: statement_source_ids(stm),
        });
        match &stm.x {
            StmX::Block(stms) => {
                // No node for the block itself; chain the children.
                // Termination-guard pairing is matched here, on the exact
                // construction vir::recursion::check_termination inserts:
                // Assert(CheckDecreaseHeight) with the Call as its immediate
                // block sibling. The guard applies to that one child only.
                let mut p = pred;
                for (i, s) in stms.iter().enumerate() {
                    self.guard_for_next = None;
                    if i > 0 {
                        if let StmX::Assert(_, _, exp) = &stms[i - 1].x {
                            if exp_has_check_decrease(exp) && matches!(&s.x, StmX::Call { .. }) {
                                let mut gp = path.clone();
                                gp.push(format!("b{}", i - 1));
                                self.guard_for_next = Some(gp.join("."));
                            }
                        }
                    }
                    path.push(format!("b{}", i));
                    p = self.walk(s, p, path);
                    path.pop();
                }
                self.guard_for_next = None;
                p
            }
            StmX::Assume(intent, exp) => {
                self.node(&id, CfgNodeKind::Assume, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                // Buffer AssertQueryEnsures for the *upcoming* region;
                // any other assume intent invalidates the buffer.
                if *intent == AssumeIntent::AssertQueryEnsures {
                    if self.lemma_span_stack.is_empty() {
                        self.pending_ensures.push(span.as_string.clone());
                    }
                } else if self.lemma_span_stack.is_empty() {
                    // Body-internal assumes must not clear the buffer: the
                    // buffered ensures belong to the region being walked.
                    self.pending_ensures.clear();
                }
                let (recognizable, sig) = (self.recognizable)(intent, exp);
                self.assumes.push(SstAssume {
                    intent: record_assume_intent(*intent),
                    span: span.as_string.clone(),
                    loop_span: self.loop_span_stack.last().cloned(),
                    lemma_span: self.lemma_span_stack.last().cloned(),
                    recognizable,
                    node: Some(id.clone()),
                    sig,
                });
                id
            }
            StmX::AssertBitVector { requires, ensures } => {
                // Prover-isolated bitvector lemma: clause spans directly on
                // the SST variant. The inner query's rows are not aligned yet
                // (different query construction); the outer joins flow
                // through the same span maps as nonlinear lemmas.
                self.node(&id, CfgNodeKind::ProofRegion, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                self.lemmas.push(LemmaRecord {
                    span: span.as_string.clone(),
                    mode: "BitVector".to_string(),
                    requires: requires.iter().map(|e| e.span.as_string.clone()).collect(),
                    ensures: ensures.iter().map(|e| e.span.as_string.clone()).collect(),
                });
                id
            }
            StmX::Assert(_, _, exp) => {
                self.node(&id, CfgNodeKind::Assert, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                let _ = exp; // guard pairing is done block-locally (Block arm)
                id
            }
            StmX::AssertCompute(..) => {
                self.node(&id, CfgNodeKind::Assert, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                id
            }
            StmX::AssertQuery { body, mode, .. } => {
                // Isolated proof region: an anonymous local lemma verified in
                // its own solver query; control passes through. The lemma's
                // requires clauses are the AssertQueryRequire-tagged assumes
                // inside the body (typed vocabulary from ast_to_sst); its
                // ensures clauses are the AssertQueryEnsures-tagged assumes
                // that follow the region in the enclosing walk.
                self.node(&id, CfgNodeKind::ProofRegion, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                // Claim the buffered ensures *before* walking the body, so
                // body-internal assumes cannot disturb them.
                let ensures = std::mem::take(&mut self.pending_ensures);
                self.lemma_span_stack.push(span.as_string.clone());
                let n_before = self.assumes.len();
                path.push("q".to_string());
                let _inner = self.walk(body, id.clone(), path);
                path.pop();
                self.lemma_span_stack.pop();
                let requires: Vec<String> = self.assumes[n_before..]
                    .iter()
                    .filter(|a| a.intent == RecordAssumeIntent::AssertQueryRequire)
                    .map(|a| a.span.clone())
                    .collect();
                self.lemmas.push(LemmaRecord {
                    span: span.as_string.clone(),
                    mode: format!("{:?}", mode),
                    requires,
                    ensures,
                });
                id
            }
            StmX::Call { fun, resolved_method, body, .. } => {
                self.node(&id, CfgNodeKind::Call, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                if let Some(guard_node) = self.guard_for_next.take() {
                    // Prefer the resolved method (trait dispatch) over the
                    // syntactic target when present.
                    let callee_fun = match (resolved_method, fun) {
                        (Some((rf, _)), _) => Some(rf),
                        (None, vir::sst::CallTarget::Fun(f)) => Some(f),
                        _ => None,
                    };
                    if let Some(f) = callee_fun {
                        self.recursive_calls.push(RecursiveCallRecord {
                            callee: super::fun_identity(f),
                            call_node: id.clone(),
                            guard_node,
                            span: span.as_string.clone(),
                            loop_span: self.loop_span_stack.last().cloned(),
                            lemma_span: self.lemma_span_stack.last().cloned(),
                        });
                    }
                }
                let callee = match fun {
                    vir::sst::CallTarget::Fun(f) => Some(super::fun_identity(f)),
                    vir::sst::CallTarget::AssumeExternal => None,
                };
                self.call_sites.push(CallSite {
                    node: id.clone(),
                    span: span.as_string.clone(),
                    callee,
                    resolved_callee: resolved_method.as_ref().map(|(f, _)| super::fun_identity(f)),
                });
                // Emplaced code executed "inside" the call (closure/atomic
                // update machinery), between pre- and post-state.
                if let Some(body) = body {
                    path.push("cb".to_string());
                    let _inner = self.walk(body, id.clone(), path);
                    path.pop();
                }
                id
            }
            StmX::If(cond, thn, els) => {
                self.node(&id, CfgNodeKind::Branch, Some(span));
                self.branches.push((id.clone(), cond.span.as_string.clone()));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                let join = format!("{}.j", id);
                self.node(&join, CfgNodeKind::Join, None);
                path.push("t".to_string());
                let t_out = self.walk(thn, id.clone(), path);
                path.pop();
                self.edge(&t_out, &join, CfgEdgeKind::Join);
                if let Some(els) = els {
                    path.push("e".to_string());
                    let e_out = self.walk(els, id.clone(), path);
                    path.pop();
                    self.edge(&e_out, &join, CfgEdgeKind::Join);
                } else {
                    self.edge(&id, &join, CfgEdgeKind::Join);
                }
                join
            }
            StmX::Loop {
                is_for_loop, id: loop_id, cond, body, invs, decrease, pre_stms, ..
            } => {
                let header = format!("{}.h", id);
                let latch = format!("{}.l", id);
                let lexit = format!("{}.x", id);
                self.node(&header, CfgNodeKind::LoopHeader, Some(span));
                self.node(&latch, CfgNodeKind::LoopLatch, None);
                self.node(&lexit, CfgNodeKind::LoopExit, None);

                let mut p = pred;
                for (i, s) in pre_stms.iter().enumerate() {
                    path.push(format!("p{}", i));
                    p = self.walk(s, p, path);
                    path.pop();
                }
                let mut cond_span = None;
                if let Some((cond_stm, cond_exp)) = cond {
                    cond_span = Some(cond_exp.span.as_string.clone());
                    path.push("c".to_string());
                    p = self.walk(cond_stm, p, path);
                    path.pop();
                }
                self.edge(&p, &header, CfgEdgeKind::Next);

                self.loops.push(LoopRecord {
                    id: *loop_id,
                    span: span.as_string.clone(),
                    invs: invs
                        .iter()
                        .map(|inv| (inv.inv.span.as_string.clone(), inv.at_entry, inv.at_exit))
                        .collect(),
                    decreases: decrease.iter().map(|d| d.span.as_string.clone()).collect(),
                    cond_span,
                    is_for_loop: *is_for_loop,
                    header: header.clone(),
                    body_entry: format!("{}.y", id),
                    latch: latch.clone(),
                    exit: lexit.clone(),
                });
                self.loop_source_ids
                    .push((*loop_id, invs.iter().map(|inv| inv.inv.span.id).collect()));

                let body_entry = format!("{}.y", id);
                self.node(&body_entry, CfgNodeKind::LoopBody, None);
                self.edge(&header, &body_entry, CfgEdgeKind::LoopBody);
                self.loop_stack.push((id.clone(), None));
                self.loop_span_stack.push(span.as_string.clone());
                path.push("yb".to_string());
                let b_out = self.walk(body, body_entry.clone(), path);
                path.pop();
                self.loop_span_stack.pop();
                self.loop_stack.pop();
                self.edge(&b_out, &latch, CfgEdgeKind::Next);
                self.edge(&latch, &header, CfgEdgeKind::LoopBack);
                self.edge(&header, &lexit, CfgEdgeKind::LoopExit);
                lexit
            }
            StmX::BreakOrContinue { is_break, .. } => {
                self.node(&id, CfgNodeKind::Transfer, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                if let Some((loop_id, _)) = self.loop_stack.last() {
                    let target =
                        if *is_break { format!("{}.x", loop_id) } else { format!("{}.l", loop_id) };
                    self.edge(&id, &target, CfgEdgeKind::Transfer);
                }
                // No fallthrough after a jump; return the jump node anyway
                // (the parent block will chain from it, matching AIR's
                // assume(false)-guarded dead code).
                id
            }
            StmX::Return { ret_exp, inside_body, .. } => {
                self.node(&id, CfgNodeKind::Return, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                if !inside_body {
                    self.implicit_return_nodes.push(id.clone());
                }
                // Construction-predicted row (same pattern as initializing
                // assigns): when the postcondition has a return destination
                // and there is postcondition work, sst_to_air::Return emits
                // `assume_var(dest, ret_exp)` — one VarEquality assume the
                // walk would otherwise not see. Negative gates: no
                // destination, no ens_exps, or no returned expression ⇒ no
                // row is predicted (returns stay unpredicted and any AIR-side
                // surplus stays Unresolved by count guard).
                if self.return_binding_emitted {
                    if let Some(e) = ret_exp {
                        self.assumes.push(SstAssume {
                            intent: RecordAssumeIntent::VarEquality,
                            span: span.as_string.clone(),
                            loop_span: self.loop_span_stack.last().cloned(),
                            lemma_span: self.lemma_span_stack.last().cloned(),
                            recognizable: false,
                            node: Some(id.clone()),
                            sig: format!("eq(var,{})", (self.sig_of)(e)),
                        });
                    }
                }
                self.edge(&id, &self.exit_id.clone(), CfgEdgeKind::Return);
                id
            }
            StmX::DeadEnd(s) => {
                self.node(&id, CfgNodeKind::DeadEnd, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                path.push("d".to_string());
                let _inner = self.walk(s, id.clone(), path);
                path.pop();
                // Facts don't escape a DeadEnd, but control does.
                id
            }
            StmX::OpenInvariant(s) => {
                self.node(&id, CfgNodeKind::Stmt, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                path.push("o".to_string());
                self.invariant_blocks.push(id.clone());
                let out = self.walk(s, id.clone(), path);
                self.invariant_blocks.pop();
                path.pop();
                out
            }
            StmX::ClosureInner { body, .. } => {
                self.node(&id, CfgNodeKind::Stmt, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                path.push("k".to_string());
                let _inner = self.walk(body, id.clone(), path);
                path.pop();
                id
            }
            StmX::Assign { lhs, rhs } if lhs.is_init => {
                // Construction-predicted row (rules::R_SST_ALIGN territory):
                // sst_to_air rewrites every initializing assign into
                // `assume_var` — an SST Assume(VarEquality, lhs == rhs)
                // lowered in place (sst_to_air.rs, StmX::Assign is_init arm).
                // The walk sees the Assign *before* that rewrite, so predict
                // the row here with the sig the rewritten equality will have.
                self.node(&id, CfgNodeKind::Assign, Some(span));
                if dest_is_synthetic(&lhs.dest) {
                    self.synthetic_bindings.push(id.clone());
                }
                self.edge(&pred, &id, CfgEdgeKind::Next);
                self.assumes.push(SstAssume {
                    intent: RecordAssumeIntent::VarEquality,
                    span: span.as_string.clone(),
                    loop_span: self.loop_span_stack.last().cloned(),
                    lemma_span: self.lemma_span_stack.last().cloned(),
                    recognizable: false,
                    node: Some(id.clone()),
                    sig: format!("eq(var,{})", (self.sig_of)(rhs)),
                });
                id
            }
            StmX::Assign { lhs, .. } => {
                // A mutating assignment: a sequential node of its own kind,
                // the site of the SSA equality the shadow run covers.
                self.node(&id, CfgNodeKind::Assign, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                if dest_is_synthetic(&lhs.dest) {
                    self.synthetic_bindings.push(id.clone());
                }
                id
            }
            // Fuel, RevealString, RevealByteString, Air, and any future leaf
            // statements: a plain sequential node.
            _ => {
                self.node(&id, CfgNodeKind::Stmt, Some(span));
                self.edge(&pred, &id, CfgEdgeKind::Next);
                id
            }
        }
    }
}

/// Is the destination of an assignment a compiler-introduced local rather
/// than a variable the user named? Decided by the variable's disambiguator,
/// which the verifier assigns at the construction that introduces the name.
fn dest_is_synthetic(dest: &Exp) -> bool {
    use vir::ast::VarIdentDisambiguate as D;
    use vir::sst::ExpX;
    match &dest.x {
        ExpX::VarLoc(ident) => matches!(
            ident.1,
            D::AirLocal
                | D::VirTemp(_)
                | D::ExpandErrorsDecl(_)
                | D::BitVectorToAirDecl(_)
                | D::ResInfTemp(_)
        ),
        _ => false,
    }
}

/// Does this SST expression contain the internal CheckDecreaseHeight call —
/// the typed identity of a termination guard (vir::recursion)?
fn exp_has_check_decrease(exp: &Exp) -> bool {
    use vir::sst::{CallFun, ExpX, InternalFun};
    let mut found = false;
    let mut check = |e: &Exp| {
        if let ExpX::Call(CallFun::InternalFun(InternalFun::CheckDecreaseHeight), _, _) = &e.x {
            found = true;
        }
    };
    fn walk(e: &Exp, f: &mut dyn FnMut(&Exp)) {
        f(e);
        match &e.x {
            vir::sst::ExpX::Call(_, _, args) => {
                for a in args.iter() {
                    walk(a, f);
                }
            }
            vir::sst::ExpX::Unary(_, a) | vir::sst::ExpX::UnaryOpr(_, a) => walk(a, f),
            vir::sst::ExpX::Binary(_, a, b) => {
                walk(a, f);
                walk(b, f);
            }
            vir::sst::ExpX::If(a, b, c) => {
                walk(a, f);
                walk(b, f);
                walk(c, f);
            }
            vir::sst::ExpX::Bind(_, a) => walk(a, f),
            _ => {}
        }
    }
    walk(exp, &mut check);
    found
}
