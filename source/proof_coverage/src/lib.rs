//! The proof-coverage consumer: turns tap events (`vir::observer`) into the
//! `verus-proof-coverage/1` record.
//!
//! All proof-coverage policy lives here, outside the verifier. Occurrence
//! provenance is assembled from three verifier-constructed signals (reserved
//! symbols, query structure, structured diagnostics — see `classify`), plus
//! SST side-tables (assume intents, ensures spans, loop invariants) emitted
//! for offline correlation and gap analysis.

pub mod verus;

// Compatibility re-exports: existing paths (`proof_coverage::analysis`,
// `crate::classify`, ...) keep working; the directory split is the
// architectural boundary.
pub use crate::verus::{cfg, classify, rules, shadow};
use proof_coverage_core::identity::{QuerySiteId, SolverToken, SsaJoin};
pub use proof_coverage_core::{analysis, audit, projection, record, rule_schema};

use air::ast::{Axiom, Command, CommandX, Commands, DeclX, Stmt, StmtX};
use air::context::{SolverReplayConfig, ValidityResult};
use classify::Classification;
use record::{
    AmbientRecord, AssertQueryPoint, AssertionPoint, ContractSection, CoverageRecord, EmissionRole,
    ForallPoint, FuelSite, FunctionRecord, InvariantBlockPoint, LoopPoint, Occurrence, QueryRecord,
    Role, SolverConfigRecord, Summary, TypeInvariantSite,
};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use vir::ast::Krate;
use vir::def::CommandContext;
use vir::observer::{
    ContextInstallReason, LocalAxiomSite, LoweringProvenance, LoweringProvenanceMap, LoweringSite,
    QueryInstanceId, SolverContextId, VerificationObserver,
};
use vir::sst::{FuncCheckSst, FunctionSst};

const OUT_ENV: &str = "VERUS_PROOF_COVERAGE_OUT";
const OUT_DEFAULT: &str = "proof-coverage.json";
const MINIMIZE_CORES_ENV: &str = "VERUS_PROOF_COVERAGE_MINIMIZE_CORES";

struct EvidenceProgress {
    total: usize,
    completed: usize,
    report_step: usize,
    next_report: usize,
    started: std::time::Instant,
    last_report: std::time::Instant,
}

impl EvidenceProgress {
    fn new(total: usize, contexts: usize) -> Self {
        let now = std::time::Instant::now();
        let report_step = (total / 20).max(100);
        if total > 0 {
            eprintln!(
                "proof-coverage: collecting solver evidence for {} eligible queries across {} {}",
                total,
                contexts,
                if contexts == 1 { "context" } else { "contexts" }
            );
        }
        Self {
            total,
            completed: 0,
            report_step,
            next_report: report_step,
            started: now,
            last_report: now,
        }
    }

    fn query_finished(&mut self) {
        self.completed = (self.completed + 1).min(self.total);
        let now = std::time::Instant::now();
        if self.completed == self.total
            || self.completed >= self.next_report
            || now.duration_since(self.last_report) >= std::time::Duration::from_secs(10)
        {
            self.report(now);
        }
    }

    fn finish_failed_context(&mut self, attempted: usize) {
        for _ in 0..attempted {
            self.query_finished();
        }
    }

    fn report(&mut self, now: std::time::Instant) {
        if self.total == 0 {
            return;
        }
        let elapsed = now.duration_since(self.started);
        let elapsed_seconds = elapsed.as_secs_f64();
        let rate =
            if elapsed_seconds > 0.0 { self.completed as f64 / elapsed_seconds } else { 0.0 };
        let eta = if rate > 0.0 {
            std::time::Duration::from_secs_f64(
                self.total.saturating_sub(self.completed) as f64 / rate,
            )
        } else {
            std::time::Duration::ZERO
        };
        eprintln!(
            "proof-coverage: evidence {}/{} queries ({:.1}%), elapsed {}, {:.1} queries/s, ETA {}",
            self.completed,
            self.total,
            100.0 * self.completed as f64 / self.total as f64,
            Self::duration(elapsed),
            rate,
            Self::duration(eta),
        );
        while self.next_report <= self.completed {
            self.next_report = self.next_report.saturating_add(self.report_step);
        }
        self.last_report = now;
    }

    fn duration(duration: std::time::Duration) -> String {
        let seconds = duration.as_secs();
        if seconds < 60 {
            format!("{seconds}s")
        } else if seconds < 60 * 60 {
            format!("{}m{:02}s", seconds / 60, seconds % 60)
        } else {
            format!("{}h{:02}m{:02}s", seconds / (60 * 60), (seconds / 60) % 60, seconds % 60)
        }
    }
}

/// A verbatim, immutable snapshot of one observer callback. Callbacks do
/// nothing else; all construction (CFG, instrumentation, attribution,
/// focused queries, shadow solving) happens in post-verification event
/// processing, driven from `on_finish`.
enum RawEvent {
    SourceInventory(Vec<SourceFunctionInventory>),
    /// AIR function identifiers paired with the friendly names the record
    /// uses, computed with the lowering's own `NameCtxt`.
    AirNames(Vec<(String, String)>),
    FunctionSst(QueryInstanceId, FunctionSst, std::sync::Arc<FuncCheckSst>),
    ContextInstalled(SolverContextId, SolverReplayConfig, ContextInstallReason, air::ast::Commands),
    Query(
        Option<QueryInstanceId>,
        SolverContextId,
        SolverReplayConfig,
        LoweringProvenance,
        CommandContext,
        air::ast::Command,
    ),
    QueryResult(Option<QueryInstanceId>, SolverContextId, &'static str),
}

#[derive(Clone)]
struct SourceFunctionInventory {
    fun: String,
    /// False for helper functions introduced by syntax expansion. They remain
    /// verifier functions but cannot contribute source artifacts/findings.
    authored: bool,
    req_spans: Vec<String>,
    ens_spans: Vec<String>,
    /// `decreases` clause spans, from pre-simplified VIR. Termination is an
    /// obligation on a clause the user wrote, so it needs a source artifact.
    dec_spans: Vec<String>,
    /// Parameter spans in declaring order. Resolves the parameter ordinal the
    /// lowering records for a type-invariant axiom when the query has no
    /// observed `FuncCheckSst` (a `spec fn` termination check).
    param_spans: Vec<String>,
    /// Everything else snapshot 1 says about the function: mode, kind,
    /// visibility, trust. Emitted as `CoverageRecord.source_functions`.
    source: record::SourceFunction,
    /// For a trait-method implementation: the trait method it refines, from
    /// `vir::ast::FunctionKind::TraitMethodImpl`. The contract clauses are
    /// declared on the trait, so the impl's obligations project onto the
    /// trait's clause artifacts through this relation.
    refines: Option<String>,
    /// Body-local source artifacts declared independently of SST/AIR.
    body_artifacts: Vec<SourceBodyArtifact>,
}

#[derive(Clone)]
struct SourceBodyArtifact {
    id: String,
    kind: record::ArtifactKind,
    span: String,
    /// Process-local VIR identities which elaborate from this one source
    /// construct. These are consumed before serialization.
    source_ids: Vec<vir::messages::AstId>,
    parent: Option<String>,
    callee: Option<String>,
    group: Option<record::LoopInvariantGroup>,
}

pub struct CoverageProducer {
    /// Passive event queue (the only thing callbacks touch).
    events: Vec<RawEvent>,
    /// Source contracts inventoried independently of whether a function
    /// later produces a verifier query.
    source_functions: Vec<SourceFunctionInventory>,
    /// AIR function identifier (as it appears in `ens%`/`req%` applications)
    /// → raw VIR path, the record's function identity. Computed by the
    /// lowering's `NameCtxt` at `on_krate`, so a callee named in the encoding
    /// is resolved by the same function that named it, not by re-spelling the
    /// identifier.
    air_names: BTreeMap<String, String>,
    functions: Vec<FunctionRecord>,
    /// Exact callback identity -> deterministic emitted SST/CFG variant.
    function_variant_by_query_instance: BTreeMap<QueryInstanceId, String>,
    /// Exact process-local SST statement identity -> deterministic CFG site,
    /// scoped by the verifier query operation that owns the SST.
    sst_sites_by_query_instance: BTreeMap<QueryInstanceId, BTreeMap<usize, cfg::SstSite>>,
    /// Most recent canonical batch emitted for one exact query operation.
    last_batch_by_query_instance: BTreeMap<QueryInstanceId, usize>,
    queries: Vec<QueryRecord>,
    ambient_batches: BTreeMap<SolverContextId, u64>,
    next_query_id: u64,
    results: BTreeMap<String, u64>,
    /// Buffered ambient commands and instrumented queries per solver context,
    /// replayed and solved at `on_finish` (an `air::Context` is not `Send`,
    /// so shadow solving cannot run under the observer lock across threads).
    shadow_events: BTreeMap<SolverContextId, Vec<shadow::ShadowEvent>>,
    /// Named ambient axioms by label, with owner and installing op.
    ambients: BTreeMap<String, AmbientRecord>,
    /// Collision guard for synthetic shadow-only ambient labels.
    ambient_fingerprints: BTreeMap<String, String>,
    /// Unnamed ambient axioms per solver context (background β tally).
    background_axioms: BTreeMap<SolverContextId, u64>,
    /// Construction-exact assert-then-assume pairs per batch query record
    /// index: (assert occurrence index, assume occurrence index). Consumed
    /// by `build_structures` to give established assertions a shared
    /// statement artifact.
    assert_pairs: BTreeMap<usize, Vec<(usize, usize, String, String)>>,
    /// Construction-exact checked exports, accumulated while structures are
    /// built and emitted as `CoverageRecord.checked_exports`.
    checked_exports: Vec<record::CheckedExport>,
    /// Completed assert-forall protocols per batch query record index:
    /// (hypothesis index, goal index, export index).
    forall_pairs: BTreeMap<usize, Vec<(usize, usize, usize)>>,
    /// Exact source projection resolved while Snapshot 2 still carries VIR
    /// span identities: (function variant, SST structural node) -> authored
    /// artifacts at that site.
    source_artifacts_by_site: BTreeMap<(String, String), Vec<String>>,
    /// Exact loop-clause projection from the declaring SST vector.
    source_loop_clauses: BTreeMap<(String, u64, usize), String>,
}

/// Walker state for one query.
struct QueryWalk<'a> {
    occurrences: Vec<Occurrence>,
    sites: Vec<QuerySiteId>,
    path: Vec<String>,
    /// Control-flow join statements (`Switch`, `Breakable`, `Break`) by path,
    /// for placing the SSA reconciliation equalities the shadow traced.
    join_stmts: BTreeMap<String, Stmt>,
    lowering_provenance: &'a LoweringProvenanceMap,
    sst_sites: Option<&'a BTreeMap<usize, cfg::SstSite>>,
    require_lowering_provenance: bool,
    missing_lowering_sites: Vec<String>,
    /// The most recent Assert seen in the current block, for the
    /// assert-then-assume pairing rule: (formula, span, occurrence index of
    /// the assert obligation in `occurrences`).
    /// The assert an assume may be pairing with: its formula, span, walk-local
    /// index, and structural path. The path is what survives: reconciliation
    /// occurrences are inserted at their join positions after this walk, so an
    /// index recorded here does not still name the same occurrence afterwards.
    last_assert: Option<(air::ast::Expr, Option<String>, usize, String)>,
    /// Construction-exact assert-then-assume pairs recorded when the
    /// asserted-proposition rule fires: (assert occurrence index, assume
    /// occurrence index). Consumed at record assembly to give established
    /// assertions a shared statement artifact.
    assert_pairs: Vec<(usize, usize, String, String)>,
    /// Assert-forall regions awaiting their exported conclusion:
    /// (goal obligation index, hypothesis premise index, expected export
    /// statement path). A `DeadEnd` whose premises open with
    /// `AssertForallRequire` is an assert-forall proof region; its last
    /// obligation is the forall goal and the next sibling statement carries
    /// the exported `AssertForallEnsures` assumption. Nesting is handled
    /// because each region records its own sibling path.
    pending_forall: Vec<(usize, usize, String)>,
    /// Completed assert-forall protocols:
    /// (hypothesis index, goal index, export index).
    forall_pairs: Vec<(usize, usize, usize)>,
    /// Loop-exit protocol arm. After `Snapshot(LOOP)` (emitted only by the
    /// loop-isolation lowering, immediately before the exit-side assumes),
    /// the entry-check expressions seen since the previous arm are the exact
    /// `Expr`s the lowering will re-assume at exit (`sst_to_air::loop_to_stmts`
    /// clones the same expression into the entry assert and the exit assume).
    /// Expression identity is therefore an exact key: no shape, no position.
    armed_exit_invs: Vec<(air::ast::Expr, String)>,
    /// Entry-check (expr, clause span) accumulated since the last arm.
    recent_establish: Vec<(air::ast::Expr, String)>,
    /// Between `Snapshot(LOOP)` and the next assert, the single `¬cond`
    /// assume is the exit condition of the same loop.
    armed_exit_cond: bool,
    /// AIR statement pointer -> emitting template slot and declared clause,
    /// recorded by the lowering sidecar at the emission point.
    emission_slots: &'a vir::observer::EmissionSlotMap,
    /// SST loop id -> every declared invariant clause span, in declaring
    /// order. Indexed by the clause ordinal the sidecar records, so the span
    /// is derived from exact identity rather than used to search for it.
    /// Several placement passes run before the artifact join and read
    /// `Occurrence.span`, so it has to be exact from the start.
    loop_clause_spans: BTreeMap<u64, Vec<String>>,
    /// AIR `Decl` pointer -> emitting construction, recorded by the lowering
    /// sidecar at each `mk_unnamed_axiom` call. This is the declaration-level
    /// counterpart of `emission_slots`: query-local axioms are not statements,
    /// so the statement-keyed maps cannot reach them.
    local_axioms: &'a vir::observer::LocalAxiomMap,
    /// Source positions the recorded ordinals resolve to: requires clauses
    /// and parameters in declaring order, loop statements by SST loop id, and
    /// the query's own span (the function or assert-query) for axioms whose
    /// site is the query itself.
    req_spans: Vec<String>,
    ens_spans: Vec<String>,
    param_spans: Vec<String>,
    loop_spans_by_id: BTreeMap<u64, String>,
    /// assert-query statement span → (requires clause spans, ensures clause
    /// spans), for the bit-vector form whose requires are query-local axioms.
    lemma_clauses: BTreeMap<String, (Vec<String>, Vec<String>)>,
    query_span: String,
}

struct ExactLowering {
    origin: record::Origin,
    role: EmissionRole,
    span: Option<String>,
    node: Option<String>,
    /// The function a type-invariant assumption applies, when the site is one.
    subject_fn: Option<String>,
}

fn unique_join<K: Ord>(map: &BTreeMap<K, Vec<String>>, key: &K) -> Option<String> {
    match map.get(key).map(Vec::as_slice) {
        Some([artifact]) => Some(artifact.clone()),
        _ => None,
    }
}

impl CoverageProducer {
    pub fn new() -> Self {
        CoverageProducer {
            events: Vec::new(),
            source_functions: Vec::new(),
            air_names: BTreeMap::new(),
            functions: Vec::new(),
            function_variant_by_query_instance: BTreeMap::new(),
            sst_sites_by_query_instance: BTreeMap::new(),
            last_batch_by_query_instance: BTreeMap::new(),
            queries: Vec::new(),
            ambient_batches: BTreeMap::new(),
            next_query_id: 0,
            results: BTreeMap::new(),
            shadow_events: BTreeMap::new(),
            ambients: BTreeMap::new(),
            ambient_fingerprints: BTreeMap::new(),
            background_axioms: BTreeMap::new(),
            assert_pairs: BTreeMap::new(),
            checked_exports: Vec::new(),
            forall_pairs: BTreeMap::new(),
            source_artifacts_by_site: BTreeMap::new(),
            source_loop_clauses: BTreeMap::new(),
        }
    }

    fn collect_pattern_source_ids(
        pattern: &vir::ast::Pattern,
        out: &mut Vec<vir::messages::AstId>,
    ) {
        use vir::ast::PatternX;
        match &pattern.x {
            PatternX::Var(_) => {
                if !pattern.span.proof_coverage_generated {
                    out.push(pattern.span.id);
                }
            }
            PatternX::Binding { sub_pat, .. } => {
                if !pattern.span.proof_coverage_generated {
                    out.push(pattern.span.id);
                }
                Self::collect_pattern_source_ids(sub_pat, out);
            }
            PatternX::MutRef(sub_pat) | PatternX::ImmutRef(sub_pat) => {
                Self::collect_pattern_source_ids(sub_pat, out);
            }
            PatternX::Constructor(_, _, fields) => {
                for field in fields.iter() {
                    Self::collect_pattern_source_ids(&field.a, out);
                }
            }
            PatternX::Or(left, right) => {
                Self::collect_pattern_source_ids(left, out);
                Self::collect_pattern_source_ids(right, out);
            }
            PatternX::Wildcard | PatternX::Expr(_) | PatternX::Range(_, _) => {}
        }
    }

    fn collect_expr_subtree_ids(expr: &vir::ast::Expr, out: &mut BTreeSet<vir::messages::AstId>) {
        let result: Result<(), ()> = vir::ast_visitor::ast_visitor_check(
            expr,
            out,
            &mut |out, _, expr| {
                out.insert(expr.span.id);
                Ok(())
            },
            &mut |out, _, stmt| {
                out.insert(stmt.span.id);
                Ok(())
            },
            &mut |out, _, pattern| {
                out.insert(pattern.span.id);
                Ok(())
            },
            &mut |_, _, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
        debug_assert!(result.is_ok());
    }

    fn source_body_inventory(
        fun: &str,
        body: &vir::ast::Expr,
        has_return_binding: bool,
    ) -> Vec<SourceBodyArtifact> {
        use record::{ArtifactKind as K, LoopInvariantGroup as G};
        use vir::ast::{ExprX, LoopInvariantKind, StmtX};

        fn implicit_return_expr(mut expr: &vir::ast::Expr) -> Option<&vir::ast::Expr> {
            loop {
                match &expr.x {
                    // Rewrites for mutable parameters and other body setup can
                    // wrap the authored body in one or more value-preserving
                    // blocks. The function result is the innermost tail, not
                    // the outer block whose span covers the entire body.
                    ExprX::Block(_, Some(tail)) => expr = tail,
                    ExprX::Block(_, None) => return None,
                    _ => return Some(expr),
                }
            }
        }

        struct Inventory<'a> {
            fun: &'a str,
            next: BTreeMap<K, usize>,
            artifacts: Vec<SourceBodyArtifact>,
        }

        impl Inventory<'_> {
            fn push(
                &mut self,
                kind: K,
                span: &vir::messages::Span,
                mut source_ids: Vec<vir::messages::AstId>,
                parent: Option<String>,
                callee: Option<String>,
                group: Option<G>,
            ) -> String {
                source_ids.sort_unstable();
                source_ids.dedup();
                let ordinal = self.next.entry(kind).or_default();
                let tag = match kind {
                    K::LoopInvariantClause => "inv",
                    K::DecreasesAggregate => "dec",
                    K::DecreasesClause => "dec_clause",
                    K::CallSite => "call",
                    K::Assertion => "assert",
                    K::AssertForall => "forall",
                    K::Assumption => "assume",
                    K::LoopCondition => "cond",
                    K::BranchCondition => "branch",
                    K::Assignment => "assign",
                    K::ReturnBinding => "return",
                    K::Reveal => "reveal",
                    K::LocalLemma => "lemma",
                    K::LemmaRequiresClause => "lemma_req",
                    K::LemmaEnsuresClause => "lemma_ens",
                    _ => "source",
                };
                let id = format!("{}#{}.src{}", self.fun, tag, *ordinal);
                *ordinal += 1;
                self.artifacts.push(SourceBodyArtifact {
                    id: id.clone(),
                    kind,
                    span: span.as_string.clone(),
                    source_ids,
                    parent,
                    callee,
                    group,
                });
                id
            }
        }

        let mut inventory = Inventory { fun, next: BTreeMap::new(), artifacts: Vec::new() };

        // Syntax expansion places automatic `for`-loop obligations alongside
        // authored loop clauses. Their roots are generated, but descendant
        // nodes can retain source-looking spans from operands used to build
        // them. Treat the generated clause root as a structural provenance
        // boundary, so no descendant can become a source artifact.
        let mut generated_clause_ids = BTreeSet::new();
        let generated_clause_result: Result<(), ()> = vir::ast_visitor::ast_visitor_check(
            body,
            &mut generated_clause_ids,
            &mut |ids, _, expr| {
                if let ExprX::Loop { invs, decrease, .. } = &expr.x {
                    for inv in invs.iter() {
                        if inv.inv.span.proof_coverage_generated {
                            Self::collect_expr_subtree_ids(&inv.inv, ids);
                        }
                    }
                    for dec in decrease.iter() {
                        if dec.span.proof_coverage_generated {
                            Self::collect_expr_subtree_ids(dec, ids);
                        }
                    }
                }
                Ok(())
            },
            &mut |_, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
            &mut |_, _, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
        debug_assert!(generated_clause_result.is_ok());

        // A function-body tail expression is the source return construct.
        // The generated SST Return must elaborate from this expression, not
        // from the enclosing block.
        if has_return_binding {
            if let Some(tail) = implicit_return_expr(body) {
                if !tail.span.proof_coverage_generated && !matches!(&tail.x, ExprX::Return(_)) {
                    inventory.push(
                        K::ReturnBinding,
                        &tail.span,
                        vec![tail.span.id],
                        Some(fun.to_string()),
                        None,
                        None,
                    );
                }
            }
        }

        let result: Result<(), ()> = vir::ast_visitor::ast_visitor_check(
            body,
            &mut inventory,
            &mut |inventory, _, expr| {
                if generated_clause_ids.contains(&expr.span.id) {
                    return Ok(());
                }
                if expr.span.proof_coverage_generated {
                    // A syntax-expanded `for` loop is itself generated, but
                    // its declaring vectors still contain the user's
                    // invariant/ensures/decreases expressions, each carrying
                    // an explicit source reset. Inventory those clauses while
                    // excluding the generated loop, condition, and automatic
                    // clauses.
                    if let ExprX::Loop { invs, decrease, .. } = &expr.x {
                        for inv in invs.iter() {
                            if inv.inv.span.proof_coverage_generated {
                                continue;
                            }
                            inventory.push(
                                K::LoopInvariantClause,
                                &inv.inv.span,
                                vec![inv.inv.span.id],
                                Some(fun.to_string()),
                                None,
                                Some(match inv.kind {
                                    LoopInvariantKind::InvariantExceptBreak => {
                                        G::InvariantExceptBreak
                                    }
                                    LoopInvariantKind::InvariantAndEnsures => G::Invariant,
                                    LoopInvariantKind::Ensures => G::LoopEnsures,
                                }),
                            );
                        }
                        let authored = decrease
                            .iter()
                            .filter(|d| !d.span.proof_coverage_generated)
                            .collect::<Vec<_>>();
                        if let Some(first) = authored.first() {
                            let aggregate = inventory.push(
                                K::DecreasesAggregate,
                                &first.span,
                                authored.iter().map(|d| d.span.id).collect(),
                                Some(fun.to_string()),
                                None,
                                None,
                            );
                            for dec in authored {
                                inventory.push(
                                    K::DecreasesClause,
                                    &dec.span,
                                    vec![dec.span.id],
                                    Some(aggregate.clone()),
                                    None,
                                    None,
                                );
                            }
                        }
                    }
                    return Ok(());
                }
                match &expr.x {
                    ExprX::Call { target, .. } => {
                        let callee = match target {
                            vir::ast::CallTarget::Fun(_, callee, ..) => {
                                Some(verus::fun_identity(callee))
                            }
                            vir::ast::CallTarget::FnSpec(_)
                            | vir::ast::CallTarget::BuiltinSpecFun(..)
                            | vir::ast::CallTarget::AssumeExternal => None,
                        };
                        inventory.push(
                            K::CallSite,
                            &expr.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            callee,
                            None,
                        );
                    }
                    ExprX::Assign { .. } => {
                        inventory.push(
                            K::Assignment,
                            &expr.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                    }
                    ExprX::AssertAssume { is_assume, expr: proposition, .. } => {
                        // A user assertion is one source construct, but AST-to-SST
                        // deliberately gives its check/establish statements the
                        // proposition's span so diagnostics highlight `P` in
                        // `assert(P)`. Define the proof-fact artifact at `P` and
                        // preserve both exact AST identities: the outer id names
                        // the written statement, while the proposition id is the
                        // identity that survives lowering to the SST sites.
                        if *is_assume {
                            inventory.push(
                                K::Assumption,
                                &expr.span,
                                vec![expr.span.id],
                                Some(fun.to_string()),
                                None,
                                None,
                            );
                        } else {
                            inventory.push(
                                K::Assertion,
                                &proposition.span,
                                vec![expr.span.id, proposition.span.id],
                                Some(fun.to_string()),
                                None,
                                None,
                            );
                        }
                    }
                    ExprX::AssertBy { ensure, .. } => {
                        inventory.push(
                            K::AssertForall,
                            &ensure.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                    }
                    ExprX::AssertQuery { requires, ensures, .. } => {
                        let lemma = inventory.push(
                            K::LocalLemma,
                            &expr.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                        for require in requires.iter() {
                            if !require.span.proof_coverage_generated {
                                inventory.push(
                                    K::LemmaRequiresClause,
                                    &require.span,
                                    vec![require.span.id],
                                    Some(lemma.clone()),
                                    None,
                                    None,
                                );
                            }
                        }
                        for ensure in ensures.iter() {
                            if !ensure.span.proof_coverage_generated {
                                inventory.push(
                                    K::LemmaEnsuresClause,
                                    &ensure.span,
                                    vec![ensure.span.id],
                                    Some(lemma.clone()),
                                    None,
                                    None,
                                );
                            }
                        }
                    }
                    ExprX::AssertCompute(proposition, ..) => {
                        inventory.push(
                            K::Assertion,
                            &proposition.span,
                            vec![expr.span.id, proposition.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                    }
                    ExprX::Fuel(..) | ExprX::RevealString(..) | ExprX::RevealByteString(..) => {
                        inventory.push(
                            K::Reveal,
                            &expr.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                    }
                    ExprX::If(cond, ..) => {
                        if !cond.span.proof_coverage_generated {
                            inventory.push(
                                K::BranchCondition,
                                &cond.span,
                                vec![cond.span.id],
                                Some(fun.to_string()),
                                None,
                                None,
                            );
                        }
                    }
                    ExprX::Match(_, arms, _) => {
                        for arm in arms.iter() {
                            let mut ids = Vec::new();
                            Self::collect_pattern_source_ids(&arm.x.pattern, &mut ids);
                            if !ids.is_empty() && !arm.x.pattern.span.proof_coverage_generated {
                                inventory.push(
                                    K::Assignment,
                                    &arm.x.pattern.span,
                                    ids,
                                    Some(fun.to_string()),
                                    None,
                                    None,
                                );
                            }
                            if !arm.x.guard.span.proof_coverage_generated
                                && !matches!(
                                    &arm.x.guard.x,
                                    ExprX::Const(vir::ast::Constant::Bool(true))
                                )
                            {
                                inventory.push(
                                    K::BranchCondition,
                                    &arm.x.guard.span,
                                    vec![arm.x.guard.span.id],
                                    Some(fun.to_string()),
                                    None,
                                    None,
                                );
                            }
                        }
                    }
                    ExprX::Loop { cond, invs, decrease, .. } => {
                        if let Some(cond) = cond {
                            if !cond.span.proof_coverage_generated {
                                inventory.push(
                                    K::LoopCondition,
                                    &cond.span,
                                    vec![cond.span.id],
                                    Some(fun.to_string()),
                                    None,
                                    None,
                                );
                            }
                        }
                        for inv in invs.iter() {
                            if inv.inv.span.proof_coverage_generated {
                                continue;
                            }
                            inventory.push(
                                K::LoopInvariantClause,
                                &inv.inv.span,
                                vec![inv.inv.span.id],
                                Some(fun.to_string()),
                                None,
                                Some(match inv.kind {
                                    LoopInvariantKind::InvariantExceptBreak => {
                                        G::InvariantExceptBreak
                                    }
                                    LoopInvariantKind::InvariantAndEnsures => G::Invariant,
                                    LoopInvariantKind::Ensures => G::LoopEnsures,
                                }),
                            );
                        }
                        let authored = decrease
                            .iter()
                            .filter(|d| !d.span.proof_coverage_generated)
                            .collect::<Vec<_>>();
                        if let Some(first) = authored.first() {
                            let aggregate = inventory.push(
                                K::DecreasesAggregate,
                                &first.span,
                                authored.iter().map(|d| d.span.id).collect(),
                                Some(fun.to_string()),
                                None,
                                None,
                            );
                            for dec in authored {
                                inventory.push(
                                    K::DecreasesClause,
                                    &dec.span,
                                    vec![dec.span.id],
                                    Some(aggregate.clone()),
                                    None,
                                    None,
                                );
                            }
                        }
                    }
                    ExprX::Return(_) if has_return_binding => {
                        inventory.push(
                            K::ReturnBinding,
                            &expr.span,
                            vec![expr.span.id],
                            Some(fun.to_string()),
                            None,
                            None,
                        );
                    }
                    _ => {}
                }
                Ok(())
            },
            &mut |inventory, _, stmt| {
                if generated_clause_ids.contains(&stmt.span.id)
                    || stmt.span.proof_coverage_generated
                {
                    return Ok(());
                }
                if let StmtX::Decl { pattern, init: Some(_), .. } = &stmt.x {
                    let mut ids = vec![stmt.span.id];
                    Self::collect_pattern_source_ids(pattern, &mut ids);
                    inventory.push(
                        K::Assignment,
                        &stmt.span,
                        ids,
                        Some(fun.to_string()),
                        None,
                        None,
                    );
                }
                Ok(())
            },
            &mut |_, _, _| Ok(()),
            &mut |_, _, _, _| Ok(()),
            &mut |_, _, _| Ok(()),
        );
        debug_assert!(result.is_ok());
        inventory.artifacts
    }

    fn solver_config_record(config: &SolverReplayConfig) -> SolverConfigRecord {
        SolverConfigRecord {
            solver: match config.solver {
                air::context::SmtSolver::Z3 => "z3",
                air::context::SmtSolver::Cvc5 => "cvc5",
            }
            .to_string(),
            options: config.option_history.clone(),
            rlimit: config.rlimit,
            single_check_query: config.single_check_query,
            ignore_unexpected_smt: config.ignore_unexpected_smt,
            debug: config.debug,
            expected_solver_version: config.expected_solver_version.clone(),
        }
    }

    /// Stable shadow-only label for a function-owned ambient axiom. The
    /// canonical AIR remains unnamed; the label is introduced only in the
    /// replayed clone. Two independent FNV-1a streams make accidental
    /// collisions auditable without relying on process-randomized hashing.
    fn ambient_label(
        op: &str,
        owner: &str,
        ordinal: usize,
        expr: &air::ast::Expr,
    ) -> (String, String) {
        let fingerprint = format!("{op}\0{owner}\0{ordinal}\0{expr:?}");
        fn fnv(bytes: &[u8], mut hash: u64) -> u64 {
            for byte in bytes {
                hash ^= u64::from(*byte);
                hash = hash.wrapping_mul(0x100000001b3);
            }
            hash
        }
        let h1 = fnv(fingerprint.as_bytes(), 0xcbf29ce484222325);
        let h2 = fnv(fingerprint.as_bytes(), 0x84222325cbf29ce4);
        (format!("pc_a%{h1:016x}{h2:016x}"), fingerprint)
    }

    fn canonical_shadow_skip_reason(results: &[String]) -> Option<&'static str> {
        if results.is_empty() {
            Some("canonical_missing")
        } else if results.iter().all(|r| r == "valid") {
            None
        } else if results.iter().any(|r| r == "type_error") {
            Some("canonical_type_error")
        } else if results.iter().any(|r| r == "unexpected_output") {
            Some("canonical_unexpected_output")
        } else if results.iter().any(|r| r == "canceled") {
            Some("canonical_canceled")
        } else {
            Some("canonical_invalid")
        }
    }

    fn collect_sst(check: &FuncCheckSst) -> cfg::SstInfo {
        cfg::build(
            check,
            &|intent, exp| (Self::sst_shape_recognizable(intent, exp), Self::sst_sig(exp)),
            &|e| Self::sst_sig(e),
        )
    }

    /// The raw VIR path of a function the encoding names by AIR identifier
    /// (`crate!impl&%1.step.` → `crate::impl&%1::step`).
    ///
    /// Exact through the `NameCtxt` table; the spelling transform below is
    /// only reached for an identifier no observed crate declared, which then
    /// resolves to no local aggregate and becomes an external artifact. That
    /// transform is the inverse of `NameCtxt`'s path spelling, so it agrees
    /// with the table rather than approximating it.
    fn path_callee(air_names: &BTreeMap<String, String>, mangled: &str) -> String {
        if let Some(path) = air_names.get(mangled) {
            return path.clone();
        }
        mangled.trim_end_matches('.').replace('!', "::").replace('.', "::")
    }

    /// Op-skeleton signature of an SST expression, comparable with
    /// `classify::air_sig` of its lowering. Box/unbox coercions and
    /// trigger annotations are transparent.
    fn sst_sig(exp: &vir::sst::Exp) -> String {
        use vir::sst::{BinaryOp, BndX, ExpX};
        match &exp.x {
            ExpX::Const(_) => "const".to_string(),
            ExpX::Var(_)
            | ExpX::StaticVar(_)
            | ExpX::VarLoc(_)
            | ExpX::VarAt(..)
            | ExpX::Old(..) => "var".to_string(),
            ExpX::Loc(e) => Self::sst_sig(e),
            ExpX::Call(..) | ExpX::CallLambda(..) | ExpX::Ctor(..) => "app".to_string(),
            ExpX::Unary(vir::ast::UnaryOp::Not, e) => format!("not({})", Self::sst_sig(e)),
            ExpX::Unary(_, e) => Self::sst_sig(e),
            ExpX::UnaryOpr(op, e) => match op {
                vir::ast::UnaryOpr::Box(_) | vir::ast::UnaryOpr::Unbox(_) => Self::sst_sig(e),
                vir::ast::UnaryOpr::HasType(_) => "app".to_string(),
                _ => "app".to_string(),
            },
            ExpX::Binary(op, a, b) => {
                let tok = match op {
                    BinaryOp::Implies => "implies",
                    BinaryOp::Eq => "eq",
                    BinaryOp::And => "and",
                    BinaryOp::Or => "or",
                    BinaryOp::Inequality(vir::ast::InequalityOp::Le) => "le",
                    BinaryOp::Inequality(vir::ast::InequalityOp::Ge) => "ge",
                    BinaryOp::Inequality(vir::ast::InequalityOp::Lt) => "lt",
                    BinaryOp::Inequality(vir::ast::InequalityOp::Gt) => "gt",
                    _ => "binop",
                };
                if tok == "and" || tok == "or" {
                    tok.to_string()
                } else {
                    format!("{}({},{})", tok, Self::sst_sig(a), Self::sst_sig(b))
                }
            }
            ExpX::If(..) => "ite".to_string(),
            ExpX::Bind(bnd, _) => match &bnd.x {
                BndX::Quant(q, ..) => match q.quant {
                    air::ast::Quant::Forall => "forall".to_string(),
                    air::ast::Quant::Exists => "exists".to_string(),
                },
                BndX::Let(..) => "let".to_string(),
                BndX::Lambda(..) => "lambda".to_string(),
                BndX::Choose(..) => "choose".to_string(),
            },
            _ => "other".to_string(),
        }
    }

    /// Recover the structured message the verifier attached to an assertion.
    fn downcast_message(msg: &air::messages::ArcDynMessage) -> Option<&vir::messages::MessageX> {
        msg.downcast_ref::<vir::messages::MessageX>()
    }

    /// Predict whether an SST assume's formula will be recognized by the
    /// AIR-side tier-1 shape rules (or the positional assert-then-assume
    /// rule), by inspecting the SST expression the same way. Used to compute
    /// the SST-side residue for order alignment.
    fn sst_shape_recognizable(intent: &vir::sst::AssumeIntent, exp: &vir::sst::Exp) -> bool {
        use vir::sst::{AssumeIntent, ExpX};
        // Positionally classified: the assume that directly follows its
        // paired assert.
        if matches!(intent, AssumeIntent::AssertedProposition | AssumeIntent::CheckedCondition) {
            return true;
        }
        match &exp.x {
            // Const/Eq shapes were AIR-side heuristics; demoted (they can
            // collide with user assume(false) / invariant equalities), so
            // those rows are no longer recognized on the AIR side and must
            // flow through alignment instead.
            ExpX::UnaryOpr(op, _) => {
                matches!(op, vir::ast::UnaryOpr::HasType(_) | vir::ast::UnaryOpr::HasResolved(_))
            }
            _ => false,
        }
    }

    fn cite_join(o: &mut Occurrence, rule: &'static str) {
        if o.artifact.is_some() && o.join_rule.is_none() {
            o.join_rule = Some(rule.to_string());
        }
    }

    /// Map an SST assume intent (site identity) to occurrence origin. The
    /// `sst:` prefix marks that provenance came through order alignment.
    fn record_assume_intent(intent: vir::sst::AssumeIntent) -> record::AssumeIntent {
        use record::AssumeIntent as R;
        use vir::sst::AssumeIntent as V;
        match intent {
            V::UserAssume => R::UserAssume,
            V::AssertedProposition => R::AssertedProposition,
            V::CheckedCondition => R::CheckedCondition,
            V::HasType => R::HasType,
            V::HasResolved => R::HasResolved,
            V::TypeInvariant => R::TypeInvariant,
            V::PathTermination => R::PathTermination,
            V::AssertForallRequire => R::AssertForallRequire,
            V::AssertForallEnsures => R::AssertForallEnsures,
            V::AssertQueryRequire => R::AssertQueryRequire,
            V::AssertQueryEnsures => R::AssertQueryEnsures,
            V::OpenedInvariant => R::OpenedInvariant,
            V::AtomicUpdate => R::AtomicUpdate,
            V::AtomicUpdateEnsures => R::AtomicUpdateEnsures,
            V::ClosureSpec => R::ClosureSpec,
            V::ClosureRequires => R::ClosureRequires,
            V::FunctionRequires => R::FunctionRequires,
            V::MutRefCurrent => R::MutRefCurrent,
            V::VarEquality => R::VarEquality,
            V::ExpandErrorsSplit => R::ExpandErrorsSplit,
        }
    }

    fn origin_of_intent(intent: record::AssumeIntent) -> record::Origin {
        use record::AssumeIntent::*;
        let kind = match intent {
            UserAssume | TypeInvariant | AssertForallRequire | AssertQueryRequire
            | OpenedInvariant | ClosureRequires | FunctionRequires => record::OriginKind::Source,
            HasType | HasResolved | PathTermination => record::OriginKind::Generated,
            AssertedProposition | CheckedCondition | AssertForallEnsures | AssertQueryEnsures
            | AtomicUpdate | AtomicUpdateEnsures | ClosureSpec | MutRefCurrent | VarEquality
            | ExpandErrorsSplit => record::OriginKind::Derived,
        };
        record::Origin { kind, detail: format!("sst:{intent:?}") }
    }

    /// The typed emission role of an SST assumption, from its construction
    /// intent. Intents with a protocol position get the finer role; the rest
    /// carry the intent itself, which is already a typed construction
    /// identity.
    fn role_of_intent(intent: record::AssumeIntent) -> EmissionRole {
        use record::AssumeIntent as I;
        match intent {
            I::UserAssume => EmissionRole::UserAssumption,
            I::AssertedProposition => EmissionRole::Assertion { point: AssertionPoint::Establish },
            I::TypeInvariant => EmissionRole::TypeInvariant { site: TypeInvariantSite::Statement },
            I::HasType => EmissionRole::HasType,
            I::HasResolved => EmissionRole::Resolution,
            I::PathTermination => EmissionRole::PathTermination,
            I::AssertForallRequire => EmissionRole::AssertForall { point: ForallPoint::Hypothesis },
            I::AssertForallEnsures => EmissionRole::AssertForall { point: ForallPoint::Establish },
            I::AssertQueryRequire => EmissionRole::AssertQuery {
                section: ContractSection::Requires,
                point: AssertQueryPoint::Assume,
            },
            I::AssertQueryEnsures => EmissionRole::AssertQuery {
                section: ContractSection::Ensures,
                point: AssertQueryPoint::Assume,
            },
            I::OpenedInvariant => EmissionRole::InvariantBlock { point: InvariantBlockPoint::Open },
            I::MutRefCurrent => EmissionRole::MutRefCurrent,
            I::VarEquality => EmissionRole::AssignmentEquality,
            I::CheckedCondition
            | I::ClosureRequires
            | I::FunctionRequires
            | I::AtomicUpdate
            | I::AtomicUpdateEnsures
            | I::ClosureSpec
            | I::ExpandErrorsSplit => EmissionRole::Assumed { intent },
        }
    }

    /// Transcribe what the pre-simplified VIR says about a function. Every
    /// field is a projection of `FunctionX`; nothing is inferred.
    fn source_function(
        fun: String,
        function: &vir::ast::Function,
        local_crate: Option<&vir::ast::CrateId>,
    ) -> record::SourceFunction {
        use vir::ast::{
            BodyVisibility as BV, CrateId, FunctionKind as FK, ItemKind as IK, Mode,
            Opaqueness as O,
        };
        // Identity comes from raw paths (`verus::fun_identity`); the friendly
        // renderings below are display metadata. `trait_path` and `module` are
        // never join keys, so they stay friendly.
        use vir::ast_util::path_as_friendly_rust_name as path_name;
        let fun_name = verus::fun_identity;
        let visibility = |v: &vir::ast::Visibility| match &v.restricted_to {
            None => record::Visibility::Public,
            Some(module) => record::Visibility::Restricted { module: path_name(module) },
        };
        let x = &function.x;
        let krate = &x.name.path.krate;
        record::SourceFunction {
            fun,
            friendly: vir::ast_util::fun_as_friendly_rust_name(&x.name),
            krate: match krate {
                CrateId::Internal => "internal".to_string(),
                CrateId::Core => "core".to_string(),
                CrateId::Alloc => "alloc".to_string(),
                CrateId::Vstd => "vstd".to_string(),
                CrateId::Id(name, _) => name.to_string(),
            },
            local: local_crate == Some(krate),
            mode: match x.mode {
                Mode::Spec => record::FunctionMode::Spec,
                Mode::Proof => record::FunctionMode::Proof,
                Mode::Exec => record::FunctionMode::Exec,
            },
            kind: match &x.kind {
                FK::Static => record::FunctionKind::Static,
                FK::TraitMethodDecl { trait_path, has_default } => {
                    record::FunctionKind::TraitMethodDecl {
                        trait_path: path_name(trait_path),
                        has_default: *has_default,
                    }
                }
                FK::TraitMethodImpl { method, trait_path, .. } => {
                    record::FunctionKind::TraitMethodImpl {
                        method: fun_name(method),
                        trait_path: path_name(trait_path),
                    }
                }
                FK::ForeignTraitMethodImpl { method, trait_path, .. } => {
                    record::FunctionKind::ForeignTraitMethodImpl {
                        method: fun_name(method),
                        trait_path: path_name(trait_path),
                    }
                }
            },
            item: match x.item_kind {
                IK::Function => record::ItemKind::Function,
                IK::Const => record::ItemKind::Const,
                IK::Static => record::ItemKind::Static,
            },
            module: x.owning_module.as_ref().map(path_name),
            visibility: visibility(&x.visibility),
            body_visibility: match &x.body_visibility {
                BV::Uninterpreted => record::BodyVisibility::Uninterpreted,
                BV::Visibility(v) => record::BodyVisibility::Visible { visibility: visibility(v) },
            },
            opaqueness: match &x.opaqueness {
                O::Opaque => record::Opaqueness::Opaque,
                O::Revealed { visibility: v } => {
                    record::Opaqueness::Revealed { visibility: visibility(v) }
                }
            },
            has_body: x.body.is_some(),
            external_body: x.attrs.is_external_body,
            broadcast: x.attrs.broadcast_forall,
            span: Some(function.span.as_string.clone()),
        }
    }

    /// Clause spans by declaring ordinal: the pre-simplified source clause
    /// when the inventory has one at that ordinal, else the SST clause.
    fn clause_spans(inventory: Option<&[String]>, sst: Option<&[String]>) -> Vec<String> {
        let inventory = inventory.unwrap_or(&[]);
        let sst = sst.unwrap_or(&[]);
        (0..inventory.len().max(sst.len()))
            .filter_map(|k| inventory.get(k).or(sst.get(k)).cloned())
            .collect()
    }

    /// Mirror a lowering template site into the record's vocabulary.
    fn lowering_site_kind(site: LoweringSite) -> record::LoweringSiteKind {
        use record::LoweringSiteKind as K;
        match site {
            LoweringSite::Assume(_) => unreachable!("assume sites carry an intent role"),
            LoweringSite::Assert => K::Assert,
            LoweringSite::AssertBitVector => K::AssertBitVector,
            LoweringSite::AssertQuery => K::AssertQuery,
            LoweringSite::AssertCompute => K::AssertCompute,
            LoweringSite::AssignInit => K::AssignInit,
            LoweringSite::AssignUpdate => K::AssignUpdate,
            LoweringSite::Call => K::Call,
            LoweringSite::Return => K::Return,
            LoweringSite::BreakOrContinue => K::BreakOrContinue,
            LoweringSite::If => K::If,
            LoweringSite::Loop => K::Loop,
            LoweringSite::OpenInvariant => K::OpenInvariant,
            LoweringSite::ClosureInner => K::ClosureInner,
            LoweringSite::Fuel => K::Fuel,
            LoweringSite::RevealString => K::RevealString,
            LoweringSite::RevealByteString => K::RevealByteString,
            LoweringSite::DeadEnd => K::DeadEnd,
            LoweringSite::Air => K::Air,
            LoweringSite::Block => K::Block,
            LoweringSite::QueryAssembly => K::QueryAssembly,
        }
    }

    /// Build the artifacts table, place occurrences onto CFG nodes, and
    /// assemble explicit derivation rows. Runs at finish, after alignment.
    fn build_structures(
        &mut self,
        alignment_derivations: Vec<(String, String)>,
    ) -> (Vec<record::Artifact>, Vec<record::Derivation>) {
        use record::{Artifact, Derivation};
        let air_names = self.air_names.clone();
        let mut artifacts: Vec<Artifact> = Vec::new();
        // (owner-scoped) span -> artifact id joins
        let mut ens_by_span: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
        // impl method -> trait method it refines (contract clauses are
        // declared on the trait).
        let refines: BTreeMap<String, String> = self
            .source_functions
            .iter()
            .filter_map(|function| {
                function.refines.as_ref().map(|target| (function.fun.clone(), target.clone()))
            })
            .collect();
        let mut req_by_idx: BTreeMap<(String, usize), String> = BTreeMap::new();
        // Local-lemma clause joins, keyed by (owner fun, clause span).
        let mut lemma_req_by_span: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
        let mut lemma_ens_by_span: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
        let mut ens_agg: BTreeMap<String, String> = BTreeMap::new();
        let mut req_agg: BTreeMap<String, String> = BTreeMap::new();
        // function -> its decreases aggregate.
        let mut dec_agg: BTreeMap<String, String> = BTreeMap::new();
        // fun -> callee -> call sites (node, span)
        let mut calls: BTreeMap<(String, String), Vec<(String, String)>> = BTreeMap::new();
        let generated_functions = self
            .source_functions
            .iter()
            .filter(|function| !function.authored)
            .map(|function| function.fun.clone())
            .collect::<BTreeSet<_>>();

        // Inventory source contracts independently of observed SST/query
        // callbacks. A source clause with no solver occurrence must remain a
        // known artifact rather than disappearing from the record.
        let mut contracts: BTreeMap<String, (Vec<String>, Vec<String>, Vec<String>)> = self
            .source_functions
            .iter()
            .filter(|function| function.authored)
            .map(|function| {
                (
                    function.fun.clone(),
                    (
                        function.req_spans.clone(),
                        function.ens_spans.clone(),
                        function.dec_spans.clone(),
                    ),
                )
            })
            .collect();
        for function in &self.functions {
            if generated_functions.contains(&function.fun) {
                continue;
            }
            // The SST-derived fallback carries no decreases spans; only the
            // pre-simplified VIR inventory has them.
            contracts.entry(function.fun.clone()).or_insert_with(|| {
                (function.req_spans.clone(), function.ens_spans.clone(), Vec::new())
            });
        }
        for (fun, (req_spans, ens_spans, dec_spans)) in contracts {
            artifacts.push(Artifact {
                id: fun.clone(),
                kind: record::ArtifactKind::Function,
                owner: fun.clone(),
                span: None,
                parent: None,
                callee: None,
                cfg_node: None,
                group: None,
            });
            let req_id = format!("{}#req", fun);
            let ens_id = format!("{}#ens", fun);
            req_agg.insert(fun.clone(), req_id.clone());
            ens_agg.insert(fun.clone(), ens_id.clone());
            artifacts.push(Artifact {
                id: req_id.clone(),
                kind: record::ArtifactKind::RequiresAggregate,
                owner: fun.clone(),
                span: None,
                parent: Some(fun.clone()),
                callee: None,
                cfg_node: None,
                group: None,
            });
            artifacts.push(Artifact {
                id: ens_id.clone(),
                kind: record::ArtifactKind::EnsuresAggregate,
                owner: fun.clone(),
                span: None,
                parent: Some(fun.clone()),
                callee: None,
                cfg_node: None,
                group: None,
            });
            for (i, span) in req_spans.iter().enumerate() {
                let id = format!("{}#req[{}]", fun, i);
                req_by_idx.insert((fun.clone(), i), id.clone());
                artifacts.push(Artifact {
                    id,
                    kind: record::ArtifactKind::RequiresClause,
                    owner: fun.clone(),
                    span: Some(span.clone()),
                    parent: Some(req_id.clone()),
                    callee: None,
                    cfg_node: None,
                    group: None,
                });
            }
            for (i, span) in ens_spans.iter().enumerate() {
                let id = format!("{}#ens[{}]", fun, i);
                ens_by_span.entry((fun.clone(), span.clone())).or_default().push(id.clone());
                artifacts.push(Artifact {
                    id,
                    kind: record::ArtifactKind::EnsuresClause,
                    owner: fun.clone(),
                    span: Some(span.clone()),
                    parent: Some(ens_id.clone()),
                    callee: None,
                    cfg_node: None,
                    group: None,
                });
            }
            // A `decreases` measure is user-authored, so its termination
            // obligation has a source subject. Lowering emits one assert for the
            // whole lexicographic tuple, so the aggregate is what the obligation
            // joins to; the components are recorded beneath it.
            if !dec_spans.is_empty() {
                let dec_id = format!("{}#dec", fun);
                dec_agg.insert(fun.clone(), dec_id.clone());
                artifacts.push(Artifact {
                    id: dec_id.clone(),
                    kind: record::ArtifactKind::DecreasesAggregate,
                    owner: fun.clone(),
                    span: None,
                    parent: Some(fun.clone()),
                    callee: None,
                    cfg_node: None,
                    group: None,
                });
                for (i, span) in dec_spans.iter().enumerate() {
                    artifacts.push(Artifact {
                        id: format!("{}#dec[{}]", fun, i),
                        kind: record::ArtifactKind::DecreasesClause,
                        owner: fun.clone(),
                        span: Some(span.clone()),
                        parent: Some(dec_id.clone()),
                        callee: None,
                        cfg_node: None,
                        group: None,
                    });
                }
            }
        }

        // Body-local source artifacts come only from Snapshot 1. Snapshot 2
        // may attach exact CFG sites to them, but may never add to this
        // population.
        let mut source_sites: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for ((_, node), artifact_ids) in &self.source_artifacts_by_site {
            for artifact_id in artifact_ids {
                source_sites.entry(artifact_id.clone()).or_default().insert(node.clone());
            }
        }
        let mut source_kind_by_id: BTreeMap<String, record::ArtifactKind> = BTreeMap::new();
        let mut source_span_by_id: BTreeMap<String, String> = BTreeMap::new();
        for source in &self.source_functions {
            if !source.authored {
                continue;
            }
            for body_artifact in &source.body_artifacts {
                let cfg_node = source_sites.get(&body_artifact.id).and_then(|nodes| {
                    let nodes = nodes.iter().cloned().collect::<Vec<_>>();
                    match nodes.as_slice() {
                        [node] => Some(node.clone()),
                        _ => None,
                    }
                });
                source_kind_by_id.insert(body_artifact.id.clone(), body_artifact.kind);
                source_span_by_id.insert(body_artifact.id.clone(), body_artifact.span.clone());
                match body_artifact.kind {
                    record::ArtifactKind::LemmaRequiresClause => {
                        lemma_req_by_span
                            .entry((source.fun.clone(), body_artifact.span.clone()))
                            .or_default()
                            .push(body_artifact.id.clone());
                    }
                    record::ArtifactKind::LemmaEnsuresClause => {
                        lemma_ens_by_span
                            .entry((source.fun.clone(), body_artifact.span.clone()))
                            .or_default()
                            .push(body_artifact.id.clone());
                    }
                    _ => {}
                }
                artifacts.push(Artifact {
                    id: body_artifact.id.clone(),
                    kind: body_artifact.kind,
                    owner: source.fun.clone(),
                    span: Some(body_artifact.span.clone()),
                    parent: body_artifact.parent.clone(),
                    callee: body_artifact.callee.clone(),
                    cfg_node,
                    group: body_artifact.group,
                });
            }
        }
        let source_projection = self.source_artifacts_by_site.clone();
        let projected_source = |variant: Option<&str>,
                                lowering_node: Option<&str>,
                                node: Option<&str>,
                                expected: &[record::ArtifactKind]|
         -> Option<String> {
            let variant = variant?;
            let node = lowering_node.or(node)?;
            let mut candidates = source_projection
                .get(&(variant.to_string(), node.to_string()))?
                .iter()
                .filter(|artifact| {
                    source_kind_by_id.get(*artifact).is_some_and(|kind| expected.contains(kind))
                })
                .cloned()
                .collect::<Vec<_>>();
            candidates.sort();
            candidates.dedup();
            match candidates.as_slice() {
                [artifact] => Some(artifact.clone()),
                _ => None,
            }
        };
        let projected_enclosing_source =
            |variant: Option<&str>, node: Option<&str>, expected: &[record::ArtifactKind]| {
                let variant = variant?;
                let mut node = node?;
                loop {
                    let mut candidates = source_projection
                        .get(&(variant.to_string(), node.to_string()))
                        .into_iter()
                        .flatten()
                        .filter(|artifact| {
                            source_kind_by_id
                                .get(*artifact)
                                .is_some_and(|kind| expected.contains(kind))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    candidates.sort();
                    candidates.dedup();
                    match candidates.as_slice() {
                        [artifact] => return Some(artifact.clone()),
                        [] => {}
                        _ => return None,
                    }
                    let Some((parent, _)) = node.rsplit_once('.') else {
                        return None;
                    };
                    node = parent;
                }
            };

        // Snapshot 2 supplies call placement and dispatch resolution only.
        // It does not manufacture call, loop, clause, or statement artifacts.
        for f in &self.functions {
            let resolved: BTreeMap<&str, &str> =
                f.resolved_calls.iter().map(|(n, r)| (n.as_str(), r.as_str())).collect();
            for (node, span, callee) in &f.call_sites {
                // Contract facts at a resolved trait call name two functions:
                // the precondition is checked against the trait method, the
                // postcondition assumed from the implementation. Both resolve
                // to this site.
                for name in
                    callee.iter().chain(resolved.get(node.as_str()).map(|r| r.to_string()).as_ref())
                {
                    calls
                        .entry((f.fun.clone(), name.clone()))
                        .or_default()
                        .push((node.clone(), span.clone()));
                }
            }
        }

        // Established assertions: the construction-exact assert-then-assume
        // pairs recorded by the walker give a user assertion's check and its
        // exported assumption one shared statement artifact, keyed by the
        // assert's CFG node (mirrors call-site identity). Only user
        // assertions (`assertion` obligations) receive source artifacts;
        // paired generated checks remain typed occurrences without invented
        // source identity. Pairs whose assert has no exact CFG placement
        // stay unjoined rather than guessing.
        {
            let pairs = std::mem::take(&mut self.assert_pairs);
            for (record_idx, pairs) in pairs {
                // Resolve by structural path, not by the walk-local index the
                // pair was recorded with: reconciliation occurrences are
                // inserted at their join positions after that walk, so an
                // index no longer names the same occurrence. A path does.
                let by_path: BTreeMap<String, usize> = self.queries[record_idx]
                    .occurrences
                    .iter()
                    .enumerate()
                    .map(|(index, occurrence)| (occurrence.path.clone(), index))
                    .collect();
                for (_, _, check_path, export_path) in pairs {
                    let (Some(&assert_index), Some(&assume_index)) =
                        (by_path.get(&check_path), by_path.get(&export_path))
                    else {
                        continue;
                    };
                    let q = &mut self.queries[record_idx];
                    // Fail closed on the roles: a checked export is an
                    // obligation licensing a premise.
                    if !matches!(
                        (q.occurrences.get(assert_index), q.occurrences.get(assume_index)),
                        (Some(check), Some(export))
                            if check.role == Role::Obligation && export.role == Role::Premise
                    ) {
                        continue;
                    }
                    let id = match &q.occurrences[assert_index] {
                        check
                            if check.origin.kind == record::OriginKind::Source
                                && check.origin.detail == "assertion" =>
                        {
                            projected_source(
                                q.function_variant.as_deref(),
                                check.lowering_node.as_deref(),
                                check.node.as_deref(),
                                &[record::ArtifactKind::Assertion],
                            )
                        }
                        _ => None,
                    };
                    // The pairing is recorded whether or not a written
                    // statement stands behind it. A generated check (overflow,
                    // pattern-match refutability, a place requirement) has no
                    // source artifact for its two halves to agree on, and
                    // dropping the pair for want of one left the export a graph
                    // root: every fact that discharged the check then fell out
                    // of every slice.
                    let kind = if id.is_some() {
                        record::CheckedExportKind::Assertion
                    } else {
                        record::CheckedExportKind::GeneratedCheck
                    };
                    if let Some((check, export)) = q.occurrences[assert_index]
                        .label
                        .clone()
                        .zip(q.occurrences[assume_index].label.clone())
                    {
                        self.checked_exports.push(record::CheckedExport {
                            kind,
                            query: q.id,
                            check,
                            export,
                        });
                    }
                    let Some(id) = id else { continue };
                    let check = &mut q.occurrences[assert_index];
                    check.artifact = Some(id.clone());
                    check.emission = Some(EmissionRole::Assertion { point: AssertionPoint::Check });
                    check.join_rule = Some(rules::R_JOIN_ASSERT.to_string());
                    let establish = &mut q.occurrences[assume_index];
                    establish.artifact = Some(id.clone());
                    establish.emission =
                        Some(EmissionRole::Assertion { point: AssertionPoint::Establish });
                    establish.join_rule = Some(rules::R_JOIN_ASSERT.to_string());
                }
            }
        }

        // Invariant blocks. An `open_atomic_invariant!` / `open_local_invariant!`
        // block assumes the invariant's contents at open and must re-establish
        // them at close, so the close obligation licenses the open assumption —
        // the same checked-export shape as an assert, one construct wider.
        //
        // The two halves are paired by recorded block membership
        // (`FunctionRecord.invariant_block_members`), which the SST walk fills
        // in while it is inside the block. Neither half has a written statement
        // behind it, so there is no artifact for them to agree on; the pairing
        // is emitted directly. A block whose open and close are not both
        // present and unique in one query is left unpaired rather than guessed.
        {
            let blocks: BTreeMap<&str, BTreeMap<&str, &str>> = self
                .functions
                .iter()
                .map(|function| {
                    let members = function
                        .invariant_block_members
                        .iter()
                        .map(|(node, block)| (node.as_str(), block.as_str()))
                        .collect();
                    (function.variant.as_str(), members)
                })
                .collect();
            let mut rows: Vec<record::CheckedExport> = Vec::new();
            for q in &self.queries {
                let Some(members) =
                    q.function_variant.as_deref().and_then(|variant| blocks.get(variant))
                else {
                    continue;
                };
                // block -> (open labels, close labels) within this query.
                let mut per_block: BTreeMap<&str, (Vec<&str>, Vec<&str>)> = BTreeMap::new();
                for occurrence in &q.occurrences {
                    let point = match occurrence.emission {
                        Some(EmissionRole::InvariantBlock { point }) => point,
                        _ => continue,
                    };
                    let (Some(node), Some(label)) =
                        (occurrence.node.as_deref(), occurrence.label.as_deref())
                    else {
                        continue;
                    };
                    let Some(block) = members.get(node) else { continue };
                    let entry = per_block.entry(block).or_default();
                    match point {
                        InvariantBlockPoint::Open => entry.0.push(label),
                        InvariantBlockPoint::Close => entry.1.push(label),
                    }
                }
                for (_, (opens, closes)) in per_block {
                    if let ([open], [close]) = (opens.as_slice(), closes.as_slice()) {
                        rows.push(record::CheckedExport {
                            kind: record::CheckedExportKind::InvariantBlock,
                            query: q.id,
                            check: close.to_string(),
                            export: open.to_string(),
                        });
                    }
                }
            }
            self.checked_exports.extend(rows);
        }

        // Assert-forall: one `assert_forall` artifact per proof region, keyed
        // by the goal's CFG node. The goal obligation, the exported
        // conclusion, and the bound-variable hypothesis all join: the region
        // is one written construct with three protocol positions.
        {
            let pairs = std::mem::take(&mut self.forall_pairs);
            for (record_idx, pairs) in pairs {
                let q = &mut self.queries[record_idx];
                for (hypothesis_index, goal_index, export_index) in pairs {
                    let (id, span) = match q.occurrences.get(goal_index) {
                        Some(goal) => {
                            let id = projected_enclosing_source(
                                q.function_variant.as_deref(),
                                goal.lowering_node.as_deref().or(goal.node.as_deref()),
                                &[record::ArtifactKind::AssertForall],
                            );
                            match (id, &goal.span) {
                                (Some(id), Some(span)) => (id, span.clone()),
                                _ => continue,
                            }
                        }
                        None => continue,
                    };
                    if q.occurrences.get(export_index).and_then(|o| o.span.as_ref()) != Some(&span)
                    {
                        // The export must carry the same asserted proposition
                        // span as its goal; otherwise leave both unjoined.
                        continue;
                    }
                    let source_span = source_span_by_id.get(&id).cloned();
                    let goal = &mut q.occurrences[goal_index];
                    goal.artifact = Some(id.clone());
                    goal.emission = Some(EmissionRole::AssertForall { point: ForallPoint::Goal });
                    goal.join_rule = Some(rules::R_JOIN_FORALL.to_string());
                    goal.span = source_span.clone();
                    let export = &mut q.occurrences[export_index];
                    export.artifact = Some(id.clone());
                    export.emission =
                        Some(EmissionRole::AssertForall { point: ForallPoint::Establish });
                    export.join_rule = Some(rules::R_JOIN_FORALL.to_string());
                    export.span = source_span.clone();
                    if let Some(hypothesis) = q.occurrences.get_mut(hypothesis_index) {
                        hypothesis.artifact = Some(id.clone());
                        hypothesis.emission =
                            Some(EmissionRole::AssertForall { point: ForallPoint::Hypothesis });
                        hypothesis.join_rule = Some(rules::R_JOIN_FORALL.to_string());
                        hypothesis.span = source_span;
                    }
                }
            }
        }

        // A function's own termination check does not need an SST variant: a
        // `spec fn` body check has none, so it has no function index, but the
        // measure is still identified by the owning function, which the query
        // carries by name. One measure per function, so this is not a guess.
        for q in &mut self.queries {
            let Some(dec) = dec_agg.get(&q.fun).cloned() else {
                continue;
            };
            for o in &mut q.occurrences {
                if o.artifact.is_none()
                    && o.emission
                        == Some(EmissionRole::TerminationCheck {
                            at: record::TerminationPoint::Function,
                        })
                {
                    o.artifact = Some(dec.clone());
                    Self::cite_join(o, rules::R_JOIN_DECREASES);
                }
            }
        }

        // External contract aggregates for callees outside this module,
        // keyed by (callee, aggregate kind) — one callee can need both.
        let mut external: BTreeMap<(String, record::ArtifactKind), ()> = BTreeMap::new();

        // Exit-condition placement: an exit-condition occurrence belongs to
        // the loop whose exit assumes immediately precede it in walk order.
        {
            let funs = &self.functions;
            let variant_index: BTreeMap<String, usize> =
                funs.iter().enumerate().map(|(i, f)| (f.variant.clone(), i)).collect();
            for q in &mut self.queries {
                let fi = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied();
                let mut last_exit_node: Option<String> = None;
                for o in &mut q.occurrences {
                    match o.phase().as_deref() {
                        Some("loop.exit_assume") => {
                            if let (Some(fi), Some(span)) = (fi, &o.span) {
                                last_exit_node = funs[fi]
                                    .loops
                                    .iter()
                                    .find(|l| l.invs.iter().any(|(s, _, _)| s == span))
                                    .map(|l| l.exit.clone());
                            }
                        }
                        Some("loop.exit_condition") => {
                            o.node = last_exit_node.clone();
                        }
                        _ => {}
                    }
                }
            }
        }
        // Recursive-call decreases join: one-to-one, count-guarded. Each
        // RecursiveCallRecord's decreases obligation shares the call span by
        // construction; exactly one such obligation may exist per record —
        // any other count leaves the row unplaced (audited downstream).
        {
            let variant_index: BTreeMap<String, usize> =
                self.functions.iter().enumerate().map(|(i, f)| (f.variant.clone(), i)).collect();
            for q in &mut self.queries {
                if q.family != record::QueryFamily::Batch {
                    continue;
                }
                let Some(fi) =
                    q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied()
                else {
                    continue;
                };
                for rc in &self.functions[fi].recursive_calls {
                    let matches: Vec<usize> = q
                        .occurrences
                        .iter()
                        .enumerate()
                        .filter(|(_, o)| {
                            o.role == record::Role::Obligation
                                && o.origin.detail == "decreases"
                                && o.span.as_deref() == Some(rc.span.as_str())
                        })
                        .map(|(i, _)| i)
                        .collect();
                    if let [i] = matches[..] {
                        let o = &mut q.occurrences[i];
                        if o.node.is_none() {
                            o.node = Some(rc.guard_node.clone());
                        }
                    }
                }
            }
        }
        // Placement + artifact joins on occurrences.
        let variant_index: BTreeMap<String, usize> =
            self.functions.iter().enumerate().map(|(i, f)| (f.variant.clone(), i)).collect();
        let source_loop_clauses = self.source_loop_clauses.clone();
        for q in &mut self.queries {
            let fi = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied();
            let q_variant = q.function_variant.clone();
            let floop = fi.and_then(|f| {
                self.functions[f].loops.iter().position(|l| l.span == q.span).map(|l| (f, l))
            });
            for o in &mut q.occurrences {
                let phase = o.phase().unwrap_or_default();
                let phase = phase.as_str();
                // Loop-protocol placement.
                if let Some((f, l)) = floop {
                    let lr = &self.functions[f].loops[l];
                    match phase {
                        "loop.body_assume" => o.node = Some(lr.body_entry.clone()),
                        "loop.maintain"
                        | "loop.decreases_at_end"
                        | "loop.decreases_at_continue"
                        | "loop.at_transfer" => o.node = Some(lr.latch.clone()),
                        _ => {}
                    }
                }
                // Exit-position placement is span-exact and applies whether
                // or not this query is itself a loop query (a loop body query
                // contains its *nested* loops' exit assumes).
                if phase == "loop.exit_assume" {
                    if let (Some(fi), Some(span)) = (fi, &o.span) {
                        if let Some(l) = self.functions[fi]
                            .loops
                            .iter()
                            .find(|l| l.invs.iter().any(|(s, _, _)| s == span))
                        {
                            o.node = Some(l.exit.clone());
                        }
                    }
                }
                if floop.is_none() && (phase == "loop.body_assume" || phase == "loop.maintain") {
                    // Non-isolated loop (no loop query): find the loop by
                    // invariant clause span.
                    if let (Some(fi), Some(span)) = (fi, &o.span) {
                        if let Some(l) = self.functions[fi]
                            .loops
                            .iter()
                            .find(|l| l.invs.iter().any(|(s, _, _)| s == span))
                        {
                            o.node = Some(if phase == "loop.maintain" {
                                l.latch.clone()
                            } else {
                                l.body_entry.clone()
                            });
                        }
                    }
                }
                if let Some(fi) = fi {
                    let f = &self.functions[fi];
                    let is_axiom = o.carrier == record::Carrier::QueryLocalAxiom;
                    match phase {
                        "function.ensures" if !is_axiom => o.node = Some(f.cfg.exit.clone()),
                        "function.requires" if !is_axiom => o.node = Some(f.cfg.entry.clone()),
                        "loop.establish" => {
                            if let Some(span) = &o.span {
                                if let Some(l) = f
                                    .loops
                                    .iter()
                                    .find(|l| l.invs.iter().any(|(s, _, _)| s == span))
                                {
                                    o.node = Some(l.header.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                }
                // Artifact joins.
                let detail = o.origin.detail.clone();
                // Exact join: the emission point recorded the clause's index in
                // the declaring `invs` vector and the owning SST loop id, so the
                // artifact identity is constructed rather than searched for. The
                // span is then taken *from* the identified clause, inverting the
                // old direction where a span was used to find the clause.
                if let (Some(fi), Some(emitted)) = (fi, o.emitted) {
                    let f = &self.functions[fi];
                    let li = emitted.loop_id.and_then(|id| f.loops.iter().position(|l| l.id == id));
                    if let Some(li) = li {
                        if emitted.slot.carries_clause() {
                            if let Some(clause) = emitted.clause {
                                if let (Some(variant), Some(loop_id)) =
                                    (q_variant.as_ref(), emitted.loop_id)
                                {
                                    o.artifact = source_loop_clauses
                                        .get(&(variant.clone(), loop_id, clause))
                                        .cloned();
                                    if let Some(span) =
                                        o.artifact.as_ref().and_then(|id| source_span_by_id.get(id))
                                    {
                                        o.span = Some(span.clone());
                                    }
                                    Self::cite_join(o, rules::R_EMITTED_CLAUSE);
                                }
                            }
                        }
                        // Exact control placement. The loop conditions are not
                        // declared clauses, so they have no artifact; the
                        // recorded loop id places them without reading a
                        // neighbour's span.
                        match emitted.slot {
                            record::EmissionSlot::LoopExitCondition => {
                                o.node = Some(f.loops[li].exit.clone());
                            }
                            record::EmissionSlot::LoopEntryCondition => {
                                o.node = Some(f.loops[li].body_entry.clone());
                            }
                            _ => {}
                        }
                    }
                }
                if let (Some(fi), Some(span)) = (fi, o.span.clone()) {
                    let span = &span;
                    let fun = self.functions[fi].fun.clone();
                    if detail == "ensures" {
                        o.artifact = unique_join(&ens_by_span, &(fun.clone(), span.clone()));
                        Self::cite_join(o, rules::R_JOIN_SPAN);
                        if o.artifact.is_none() {
                            if let Some(target) = refines.get(&fun) {
                                o.artifact =
                                    unique_join(&ens_by_span, &(target.clone(), span.clone()));
                                Self::cite_join(o, rules::R_JOIN_REFINEMENT);
                            }
                        }
                    } else if detail == "decreases" {
                        // Function termination has one declaration-owned
                        // aggregate. Loop measures are joined below through
                        // exact source-to-SST site provenance.
                        if o.emission
                            == Some(EmissionRole::TerminationCheck {
                                at: record::TerminationPoint::Function,
                            })
                        {
                            o.artifact = dec_agg.get(&fun).cloned();
                            Self::cite_join(o, rules::R_JOIN_DECREASES);
                        }
                    } else if detail == "sst:AssertQueryRequire" {
                        // Inner premise: the lemma's hypothesis, assumed.
                        o.artifact = unique_join(&lemma_req_by_span, &(fun.clone(), span.clone()));
                        Self::cite_join(o, rules::R_JOIN_LEMMA_SPAN);
                    } else if detail == "sst:AssertQueryEnsures" {
                        // Outer premise: the lemma's conclusion, consumed.
                        o.artifact = unique_join(&lemma_ens_by_span, &(fun.clone(), span.clone()));
                        Self::cite_join(o, rules::R_JOIN_LEMMA_SPAN);
                    } else if o.role == record::Role::Obligation {
                        // Outer requires check / inner goal, joined by clause
                        // span. Exact: the same spans the SST region reported.
                        if let Some(a) =
                            unique_join(&lemma_req_by_span, &(fun.clone(), span.clone()))
                        {
                            o.artifact = Some(a);
                            o.rule = Some(rules::R_JOIN_LEMMA_SPAN.to_string());
                            o.join_rule = Some(rules::R_JOIN_LEMMA_SPAN.to_string());
                            o.origin = record::Origin {
                                kind: record::OriginKind::Source,
                                detail: "lemma_requires".to_string(),
                            };
                            o.emission = Some(EmissionRole::AssertQuery {
                                section: ContractSection::Requires,
                                point: AssertQueryPoint::Check,
                            });
                            o.shape = None;
                        } else if let Some(a) =
                            unique_join(&lemma_ens_by_span, &(fun.clone(), span.clone()))
                        {
                            o.artifact = Some(a);
                            o.rule = Some(rules::R_JOIN_LEMMA_SPAN.to_string());
                            o.join_rule = Some(rules::R_JOIN_LEMMA_SPAN.to_string());
                            o.origin = record::Origin {
                                kind: record::OriginKind::Source,
                                detail: "lemma_goal".to_string(),
                            };
                            o.emission = Some(EmissionRole::AssertQuery {
                                section: ContractSection::Ensures,
                                point: AssertQueryPoint::Check,
                            });
                            o.shape = None;
                        }
                    }
                }
                if o.artifact.is_none() {
                    let expected: &[record::ArtifactKind] = match &o.emission {
                        Some(EmissionRole::UserAssumption) => &[record::ArtifactKind::Assumption],
                        Some(EmissionRole::AssignmentEquality | EmissionRole::MutationEquality) => {
                            &[record::ArtifactKind::Assignment, record::ArtifactKind::ReturnBinding]
                        }
                        Some(EmissionRole::Fuel { site: FuelSite::Statement }) => {
                            &[record::ArtifactKind::Reveal]
                        }
                        Some(EmissionRole::BranchCondition { .. }) => {
                            &[record::ArtifactKind::BranchCondition]
                        }
                        Some(
                            EmissionRole::LoopEntryCondition | EmissionRole::LoopExitCondition,
                        ) => &[record::ArtifactKind::LoopCondition],
                        Some(EmissionRole::Assertion { .. }) => &[record::ArtifactKind::Assertion],
                        Some(EmissionRole::AssertForall { .. }) => {
                            &[record::ArtifactKind::AssertForall]
                        }
                        Some(EmissionRole::TerminationCheck {
                            at:
                                record::TerminationPoint::LoopEnd
                                | record::TerminationPoint::LoopContinue,
                        }) => &[record::ArtifactKind::DecreasesAggregate],
                        _ => &[],
                    };
                    if !expected.is_empty() {
                        o.artifact = projected_source(
                            q_variant.as_deref(),
                            o.lowering_node.as_deref(),
                            o.node.as_deref(),
                            expected,
                        );
                        let join_rule = match o.emission {
                            Some(
                                EmissionRole::LoopEntryCondition | EmissionRole::LoopExitCondition,
                            ) => rules::R_JOIN_LOOP_COND,
                            Some(EmissionRole::TerminationCheck { .. }) => rules::R_JOIN_DECREASES,
                            _ => rules::R_SOURCE_PROVENANCE,
                        };
                        Self::cite_join(o, join_rule);
                    }
                }
                if let Some(rest) = detail.strip_prefix("requires[") {
                    if let (Some(fi), Some(k)) =
                        (fi, rest.strip_suffix(']').and_then(|s| s.parse::<usize>().ok()))
                    {
                        let fun = self.functions[fi].fun.clone();
                        o.artifact = req_by_idx.get(&(fun.clone(), k)).cloned();
                        // The ordinal is exact identity when the sidecar
                        // recorded it, and a positional pairing otherwise.
                        if o.rule.as_deref() == Some(rules::R_EMITTED_AXIOM) {
                            Self::cite_join(o, rules::R_EMITTED_CLAUSE);
                        } else {
                            Self::cite_join(o, rules::R_JOIN_REQ_IDX);
                        }
                        if o.artifact.is_none() {
                            if let Some(target) = refines.get(&fun) {
                                o.artifact = req_by_idx.get(&(target.clone(), k)).cloned();
                                Self::cite_join(o, rules::R_JOIN_REFINEMENT);
                            }
                        }
                    }
                }
                // Contract aggregates for cross-boundary facts; single-site
                // placement when the caller has exactly one site for the callee.
                let (agg_map, callee, is_ens): (&BTreeMap<String, String>, Option<String>, bool) =
                    if let Some(g) = detail.strip_prefix("ensures_of:") {
                        (&ens_agg, Some(Self::path_callee(&air_names, g)), true)
                    } else if let Some(g) = detail.strip_prefix("requires_of:") {
                        (&req_agg, Some(Self::path_callee(&air_names, g)), false)
                    } else {
                        (&ens_agg, None, false)
                    };
                if let Some(g) = callee {
                    // The role names the callee the way the record does, and
                    // the diagnostic detail follows it rather than keeping the
                    // AIR spelling.
                    o.emission = Some(if is_ens {
                        EmissionRole::CallPostcondition { callee: g.clone() }
                    } else {
                        EmissionRole::CallPrecondition { callee: Some(g.clone()) }
                    });
                    o.origin.detail =
                        format!("{}:{}", if is_ens { "ensures_of" } else { "requires_of" }, g);
                    o.artifact = agg_map.get(&g).cloned().or_else(|| {
                        external.insert(
                            (
                                g.clone(),
                                if is_ens {
                                    record::ArtifactKind::EnsuresAggregate
                                } else {
                                    record::ArtifactKind::RequiresAggregate
                                },
                            ),
                            (),
                        );
                        Some(format!("{}#{}", g, if is_ens { "ens" } else { "req" }))
                    });
                    Self::cite_join(o, rules::R_JOIN_AGGREGATE);
                    if o.node.is_none() {
                        if let Some(fi) = fi {
                            let fun = self.functions[fi].fun.clone();
                            if let Some(sites) = calls.get(&(fun, g.clone())) {
                                if sites.len() == 1 {
                                    o.node = Some(sites[0].0.clone());
                                }
                            }
                        }
                    }
                }
            }
        }

        // Call-site attribution: within one query region, the k-th
        // call-post premise (or call-pre obligation) for callee g pairs with
        // the k-th call site to g in structural order — applied only when
        // the counts agree exactly.
        for q in &mut self.queries {
            if q.family != record::QueryFamily::Batch {
                continue;
            }
            let Some(fi) = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied()
            else {
                continue;
            };
            let f = &self.functions[fi];
            // Region filter: a site is in this query iff its loop-membership
            // matches (loop query ⇒ inside that loop; body query ⇒ outside
            // all isolated loops). Loop membership from the node path: the
            // loop's structural base is its header minus ".h".
            let loop_base: Option<String> = f
                .loops
                .iter()
                .find(|l| l.span == q.span)
                .map(|l| l.header.strip_suffix(".h").unwrap_or(&l.header).to_string());
            let isolated_bases: Vec<String> = f
                .loops
                .iter()
                .map(|l| l.header.strip_suffix(".h").unwrap_or(&l.header).to_string())
                .collect();
            let site_in_region = |node: &str| -> bool {
                match &loop_base {
                    Some(base) => node.starts_with(base.as_str()),
                    None => !isolated_bases.iter().any(|b| node.starts_with(b.as_str())),
                }
            };

            // First use the lowering's local call-contract block. Requires
            // checks and the following ensures assumption are siblings in
            // one AIR block; the requires checks retain the exact source call
            // span even when method resolution gives the AIR callee a
            // different internal impl name than SST. If that span selects
            // exactly one SST call site in this query region, place the whole
            // sibling group there. This is construction identity, not a
            // formula/name heuristic.
            let mut contract_groups: BTreeMap<String, Vec<usize>> = BTreeMap::new();
            for (i, o) in q.occurrences.iter().enumerate() {
                if o.node.is_some()
                    || !(o.origin.detail.starts_with("requires_of:")
                        || o.origin.detail.starts_with("ensures_of:"))
                {
                    continue;
                }
                if let Some((parent, child)) = o.path.rsplit_once('.') {
                    if child.strip_prefix('b').is_some_and(|index| {
                        !index.is_empty() && index.bytes().all(|b| b.is_ascii_digit())
                    }) {
                        contract_groups.entry(parent.to_string()).or_default().push(i);
                    }
                }
            }
            for indices in contract_groups.values() {
                let spans: BTreeSet<&str> = indices
                    .iter()
                    .filter_map(|&i| {
                        let o = &q.occurrences[i];
                        o.origin
                            .detail
                            .starts_with("requires_of:")
                            .then(|| o.span.as_deref())
                            .flatten()
                    })
                    .collect();
                let [span] = spans.iter().copied().collect::<Vec<_>>()[..] else {
                    continue;
                };
                let sites: Vec<&String> = f
                    .call_sites
                    .iter()
                    .filter(|(node, site_span, _)| site_span == span && site_in_region(node))
                    .map(|(node, _, _)| node)
                    .collect();
                if let [node] = sites[..] {
                    for &i in indices {
                        q.occurrences[i].node = Some(node.clone());
                    }
                }
            }

            for dir in ["ensures_of:", "requires_of:"] {
                let mut per_callee: BTreeMap<String, Vec<usize>> = BTreeMap::new();
                for (i, o) in q.occurrences.iter().enumerate() {
                    if o.node.is_some() {
                        continue;
                    }
                    if let Some(g) = o.origin.detail.strip_prefix(dir) {
                        per_callee.entry(Self::path_callee(&air_names, g)).or_default().push(i);
                    }
                }
                for (g, occ_idxs) in per_callee {
                    let resolved: BTreeMap<&str, &str> =
                        f.resolved_calls.iter().map(|(n, r)| (n.as_str(), r.as_str())).collect();
                    let sites: Vec<&String> = f
                        .call_sites
                        .iter()
                        .filter(|(node, _, callee)| {
                            (callee.as_deref() == Some(g.as_str())
                                || resolved.get(node.as_str()) == Some(&g.as_str()))
                                && site_in_region(node)
                        })
                        .map(|(node, _, _)| node)
                        .collect();
                    if sites.len() == occ_idxs.len() {
                        for (k, &i) in occ_idxs.iter().enumerate() {
                            q.occurrences[i].node = Some(sites[k].clone());
                        }
                    }
                }
            }
        }

        // The exact lowering sidecar can identify a post-transform SST
        // statement that is absent from the recorded source CFG. Such a site
        // is useful internally, but it is not a resolvable record identity.
        // Keep any independently justified control placement, and withhold
        // the lowering edge unless its input resolves in this function
        // variant's CFG.
        for q in &mut self.queries {
            let Some(fi) = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied()
            else {
                continue;
            };
            let valid: BTreeSet<&str> =
                self.functions[fi].cfg.nodes.iter().map(|node| node.id.as_str()).collect();
            for occurrence in &mut q.occurrences {
                if occurrence.node.as_deref().is_some_and(|node| !valid.contains(node)) {
                    occurrence.node = None;
                }
                if occurrence.lowering_node.as_deref().is_some_and(|node| !valid.contains(node)) {
                    occurrence.lowering_node = None;
                }
            }
        }

        let function_artifacts: BTreeSet<String> = artifacts
            .iter()
            .filter(|a| a.kind == record::ArtifactKind::Function)
            .map(|a| a.id.clone())
            .collect();
        // Type-invariant assumptions name a declaration, not a body-local
        // source construct, so their exact subject remains the function
        // artifact. All statement-like subjects were already joined from the
        // independent source inventory above.
        for q in &mut self.queries {
            for o in &mut q.occurrences {
                if o.artifact.is_none()
                    && matches!(o.emission, Some(EmissionRole::TypeInvariant { .. }))
                    && o.subject_fn
                        .as_ref()
                        .is_some_and(|subject| function_artifacts.contains(subject))
                {
                    o.artifact = o.subject_fn.clone();
                    o.join_rule = Some(rules::R_JOIN_TYPE_INVARIANT.to_string());
                }
            }
        }

        for ((g, kind), ()) in external {
            let suffix = if kind == record::ArtifactKind::EnsuresAggregate { "ens" } else { "req" };
            artifacts.push(record::Artifact {
                id: format!("{}#{}", g, suffix),
                kind,
                owner: g,
                span: None,
                parent: None,
                callee: None,
                cfg_node: None,
                group: None,
            });
        }
        artifacts.sort_by(|a, b| a.id.cmp(&b.id).then(a.kind.cmp(&b.kind)));
        artifacts.dedup_by(|a, b| a.id == b.id && a.kind == b.kind);

        // Derivations: terminal splits + exact and fallback lowerings.
        let mut derivations: Vec<Derivation> = Vec::new();
        for q in &self.queries {
            if q.family == record::QueryFamily::Focused {
                if let (Some(parent), Some(target)) = (&q.parent_obligation_label, &q.target_label)
                {
                    derivations.push(Derivation {
                        transform: record::Transform::TerminalSplit,
                        inputs: vec![parent.clone()],
                        outputs: vec![target.clone()],
                    });
                }
            }
            if q.family == record::QueryFamily::Batch {
                for occurrence in &q.occurrences {
                    if let (Some(variant), Some(node), Some(label)) = (
                        q.function_variant.as_deref(),
                        &occurrence.lowering_node,
                        &occurrence.label,
                    ) {
                        derivations.push(Derivation {
                            transform: record::Transform::LowerStatement,
                            inputs: vec![format!("{}:{}", variant, node)],
                            outputs: vec![label.clone()],
                        });
                    }
                }
            }
        }
        for (input, output) in alignment_derivations {
            derivations.push(Derivation {
                transform: record::Transform::LowerAssume,
                inputs: vec![input],
                outputs: vec![output],
            });
        }
        (artifacts, derivations)
    }

    /// Order-based SST alignment (`PROOF_COVERAGE.md` §3): for each
    /// batch query, the unclassified statement assumes are matched, in order,
    /// against the SST assume sequence the query lowers (function body
    /// outside loops, or one loop body). Applied only when the counts agree
    /// exactly; any mismatch leaves every row unresolved and is counted.
    fn align_sst(&mut self) -> (u64, u64, Vec<(String, String)>) {
        let variant_index: BTreeMap<String, usize> =
            self.functions.iter().enumerate().map(|(i, f)| (f.variant.clone(), i)).collect();
        let mut aligned = 0u64;
        let mut mismatched_queries = 0u64;
        let mut alignment_derivations: Vec<(String, String)> = Vec::new();
        for q in &mut self.queries {
            if q.family != record::QueryFamily::Batch {
                continue;
            }
            let Some(fi) = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied()
            else {
                continue;
            };
            let f = &self.functions[fi];
            let is_loop_query = f.loops.iter().any(|l| l.span == q.span);
            // SST-side sequence for this query.
            let sst_side: Vec<(&record::AssumeIntent, &String, Option<&String>, &String)> = if q
                .desc
                == "function body check"
            {
                f.sst_assumes
                    .iter()
                    .filter(|a| a.loop_span.is_none() && a.lemma_span.is_none() && !a.recognizable)
                    .map(|a| (&a.intent, &a.span, a.node.as_ref(), &a.sig))
                    .collect()
            } else if is_loop_query {
                f.sst_assumes
                    .iter()
                    .filter(|a| {
                        a.loop_span.as_ref() == Some(&q.span)
                            && a.lemma_span.is_none()
                            && !a.recognizable
                    })
                    .map(|a| (&a.intent, &a.span, a.node.as_ref(), &a.sig))
                    .collect()
            } else if q.desc == "assert_nonlinear_by" && f.lemmas.iter().any(|l| l.span == q.span) {
                // Prover-isolated local lemma: its body rows lower into
                // this query, keyed by the assert-query span.
                f.sst_assumes
                    .iter()
                    .filter(|a| a.lemma_span.as_ref() == Some(&q.span) && !a.recognizable)
                    .map(|a| (&a.intent, &a.span, a.node.as_ref(), &a.sig))
                    .collect()
            } else {
                continue;
            };
            // Requires alignment for query-local axioms (function body only).
            if q.desc == "function body check" {
                let unresolved_local: Vec<usize> = q
                    .occurrences
                    .iter()
                    .enumerate()
                    .filter(|(_, o)| {
                        o.carrier == record::Carrier::QueryLocalAxiom
                            && o.origin.kind == record::OriginKind::Unresolved
                    })
                    .map(|(i, _)| i)
                    .collect();
                if unresolved_local.len() == f.req_spans.len() {
                    for (k, &i) in unresolved_local.iter().enumerate() {
                        let o = &mut q.occurrences[i];
                        o.origin = record::Origin {
                            kind: record::OriginKind::Source,
                            detail: format!("requires[{}]", k),
                        };
                        o.rule = Some(rules::R_SST_ALIGN.to_string());
                        o.emission = Some(EmissionRole::FunctionRequires { clause: k as u32 });
                        o.span = Some(f.req_spans[k].clone());
                        o.shape = None;
                        aligned += 1;
                    }
                }
            }
            // Statement assume alignment.
            let unresolved_stmts: Vec<usize> = q
                .occurrences
                .iter()
                .enumerate()
                .filter(|(_, o)| {
                    o.carrier == record::Carrier::Assume
                        && o.origin.kind == record::OriginKind::Unresolved
                })
                .map(|(i, _)| i)
                .collect();
            if unresolved_stmts.is_empty() {
                continue;
            }
            // SST side minus rows the shape/positional rules account for
            // (predicted per-row at collect time from the SST expression).
            let sst_unrecognizable: Vec<(
                &record::AssumeIntent,
                &String,
                Option<&String>,
                &String,
            )> = sst_side;
            // This query is linked to the exact FuncCheckSst variant that
            // lowering consumed. Within that instance, lowering preserves
            // statement order; exact residue-count agreement therefore
            // identifies the rows without relying on formula-shape equality.
            let exact_order = unresolved_stmts.len() == sst_unrecognizable.len();
            if exact_order {
                for (k, &i) in unresolved_stmts.iter().enumerate() {
                    let (intent, span, node, _) = &sst_unrecognizable[k];
                    let o = &mut q.occurrences[i];
                    o.origin = Self::origin_of_intent(**intent);
                    o.rule = Some(rules::R_SST_ALIGN.to_string());
                    o.span = Some((*span).clone());
                    o.node = node.map(|n| n.clone());
                    o.shape = None;
                    if let (Some(node), Some(label)) = (node, &o.label) {
                        alignment_derivations
                            .push((format!("{}:{}", f.variant, node), label.clone()));
                    }
                    aligned += 1;
                }
            } else {
                // Per-signature-bucket fallback: within each op-skeleton
                // signature, match in order when that bucket's counts agree.
                let mut sst_buckets: BTreeMap<&String, Vec<usize>> = BTreeMap::new();
                for (k, (_, _, _, sig)) in sst_unrecognizable.iter().enumerate() {
                    sst_buckets.entry(sig).or_default().push(k);
                }
                let mut air_buckets: BTreeMap<String, Vec<usize>> = BTreeMap::new();
                for &i in &unresolved_stmts {
                    if let Some(sig) = &q.occurrences[i].sig {
                        air_buckets.entry(sig.clone()).or_default().push(i);
                    }
                }
                let mut bucket_aligned = 0u64;
                for (sig, occ_is) in &air_buckets {
                    let Some(sst_is) = sst_buckets.get(sig) else { continue };
                    if sst_is.len() != occ_is.len() {
                        continue;
                    }
                    for (k, &i) in occ_is.iter().enumerate() {
                        let (intent, span, node, _) = &sst_unrecognizable[sst_is[k]];
                        let o = &mut q.occurrences[i];
                        o.origin = Self::origin_of_intent(**intent);
                        o.rule = Some(rules::R_SST_SIGBUCKET.to_string());
                        o.span = Some((*span).clone());
                        o.node = node.map(|n| n.clone());
                        o.shape = None;
                        if let (Some(node), Some(label)) = (node, &o.label) {
                            alignment_derivations
                                .push((format!("{}:{}", f.variant, node), label.clone()));
                        }
                        bucket_aligned += 1;
                    }
                }
                aligned += bucket_aligned;
                if (bucket_aligned as usize) < unresolved_stmts.len() {
                    mismatched_queries += 1;
                }
            }
        }
        // Const-false exclusion (R_CONST_FALSE_EXCLUSION): AIR-synthesized
        // const-false assumes (loop_end, dead ends) have no SST rows, so
        // order alignment cannot type them. But `assume(false)` written by
        // the user *does* have an SST row (UserAssume). If a query's region
        // has zero SST rows whose expression is const-false, then every
        // const-false AIR row in that query is synthesized path termination
        // — by exclusion, not by shape. If the region has any, we cannot
        // tell which AIR row is whose: all stay Unresolved.
        for q in &mut self.queries {
            if q.family != record::QueryFamily::Batch {
                continue;
            }
            let Some(fi) = q.function_variant.as_ref().and_then(|v| variant_index.get(v)).copied()
            else {
                continue;
            };
            let f = &self.functions[fi];
            let is_loop_query = f.loops.iter().any(|l| l.span == q.span);
            let in_region = |a: &record::SstAssume| -> bool {
                if q.desc == "function body check" {
                    a.loop_span.is_none() && a.lemma_span.is_none()
                } else if is_loop_query {
                    a.loop_span.as_ref() == Some(&q.span) && a.lemma_span.is_none()
                } else {
                    a.lemma_span.as_ref() == Some(&q.span)
                }
            };
            // Only a *user-written* const assume makes the region ambiguous:
            // SST PathTermination rows are const-sig too, but they support
            // the same conclusion, and assert(false)-derived assumes are
            // already attributed positionally.
            let ambiguous = f.sst_assumes.iter().any(|a| {
                in_region(a) && a.sig == "const" && a.intent == record::AssumeIntent::UserAssume
            });
            if ambiguous {
                continue;
            }
            for o in &mut q.occurrences {
                if o.origin.kind == record::OriginKind::Unresolved
                    && o.origin.detail == "const_false"
                {
                    o.origin = record::Origin {
                        kind: record::OriginKind::Generated,
                        detail: "path_termination".to_string(),
                    };
                    o.emission = Some(EmissionRole::PathTermination);
                    o.rule = Some(rules::R_CONST_FALSE_EXCLUSION.to_string());
                    o.shape = None;
                }
            }
        }
        (aligned, mismatched_queries, alignment_derivations)
    }
}

impl<'a> QueryWalk<'a> {
    fn lowering(&self, stmt: &Stmt) -> Option<&vir::observer::LoweredStatement> {
        self.lowering_provenance.get(&(Arc::as_ptr(stmt) as usize))
    }

    /// The slot and declared clause the lowering recorded for this statement.
    ///
    /// Construction-exact: recorded at the emission point in `sst_to_air`,
    /// where the slot is a compile-time constant and the clause is the loop
    /// variable. Nothing is inferred from statement order, shape, or span.
    fn emitted_clause(&self, stmt: &Stmt) -> Option<record::EmittedClause> {
        use record::EmissionSlot as R;
        use vir::observer::EmissionSlot as V;
        let emitted = self.emission_slots.get(&(Arc::as_ptr(stmt) as usize))?;
        let slot = match emitted.slot {
            V::LoopEstablish => R::LoopEstablish,
            V::LoopBodyEntry => R::LoopBodyEntry,
            V::LoopMaintain => R::LoopMaintain,
            V::LoopExit => R::LoopExit,
            V::LoopAtBreak => R::LoopAtBreak,
            V::LoopAtContinue => R::LoopAtContinue,
            V::LoopEntryCondition => R::LoopEntryCondition,
            V::LoopExitCondition => R::LoopExitCondition,
            V::BranchThen => R::BranchThen,
            V::BranchElse => R::BranchElse,
            V::BitVectorFunctionEnsures => R::BitVectorFunctionEnsures,
            V::BitVectorAssertQueryEnsures => R::BitVectorAssertQueryEnsures,
        };
        Some(record::EmittedClause { slot, clause: emitted.clause, loop_id: emitted.loop_id })
    }

    fn exact_lowering(&self, stmt: &Stmt) -> Option<ExactLowering> {
        let provenance = self.lowering(stmt)?;
        let site = self.sst_sites.and_then(|sites| {
            provenance.source_chain.iter().rev().find_map(|frame| sites.get(&frame.statement))
        });
        let intent = provenance.source_chain.iter().rev().find_map(|frame| match frame.site {
            LoweringSite::Assume(intent) => Some(intent),
            _ => None,
        });
        let (origin, role) = if let Some(intent) = intent {
            let intent = CoverageProducer::record_assume_intent(intent);
            (CoverageProducer::origin_of_intent(intent), CoverageProducer::role_of_intent(intent))
        } else {
            let kind = if provenance.emitted_at == LoweringSite::QueryAssembly {
                record::OriginKind::Generated
            } else {
                record::OriginKind::Derived
            };
            (
                record::Origin { kind, detail: format!("lowering:{:?}", provenance.emitted_at) },
                EmissionRole::Lowered {
                    site: CoverageProducer::lowering_site_kind(provenance.emitted_at),
                },
            )
        };
        Some(ExactLowering {
            origin,
            role,
            span: site.map(|site| site.span.clone()),
            node: site.map(|site| site.node.clone()),
            subject_fn: site.and_then(|site| site.subject_fn.clone()),
        })
    }

    fn walk(&mut self, stmt: &Stmt) {
        match &**stmt {
            StmtX::Assume(expr) => {
                if self.require_lowering_provenance && self.lowering(stmt).is_none() {
                    self.missing_lowering_sites.push(self.path.join("."));
                }
                let mut class = classify::classify_premise(expr);
                let emitted = self.emitted_clause(stmt);
                let mut span = None;
                // Rule (construction-exact): the lowering recorded which named
                // slot of which template emitted this statement. The slot is a
                // compile-time constant at the emission point, so this needs no
                // arming, no ordering assumption, and no span. It runs before
                // every positional rule and supersedes them.
                if let Some(emitted) = emitted {
                    use record::EmissionSlot as S;
                    let named = match emitted.slot {
                        S::LoopEstablish
                        | S::LoopBodyEntry
                        | S::LoopMaintain
                        | S::LoopExit
                        | S::LoopAtBreak
                        | S::LoopAtContinue => Some((record::OriginKind::Source, "loop_invariant")),
                        S::LoopEntryCondition => {
                            Some((record::OriginKind::Source, "loop_entry_condition"))
                        }
                        S::LoopExitCondition => {
                            Some((record::OriginKind::Source, "loop_exit_condition"))
                        }
                        S::BranchThen | S::BranchElse => {
                            Some((record::OriginKind::Derived, "branch_condition"))
                        }
                        // Assert slots; an assumption never carries them.
                        S::BitVectorFunctionEnsures | S::BitVectorAssertQueryEnsures => None,
                    };
                    if let Some((kind, detail)) = named {
                        class = Classification {
                            origin: record::Origin { kind, detail: detail.to_string() },
                            role: Some(emitted.slot.role()),
                            rule: rules::R_EMITTED_SLOT,
                        };
                        // The span follows from the identity, not the reverse.
                        if span.is_none() {
                            if let (Some(loop_id), Some(clause)) = (emitted.loop_id, emitted.clause)
                            {
                                span = self
                                    .loop_clause_spans
                                    .get(&loop_id)
                                    .and_then(|spans| spans.get(clause))
                                    .cloned();
                            }
                        }
                        // Keep the positional machine's queues consistent so a
                        // leftover cannot re-attribute a claimed statement.
                        if let Some(k) = self
                            .armed_exit_invs
                            .iter()
                            .position(|(e, _)| std::sync::Arc::ptr_eq(e, expr))
                        {
                            self.armed_exit_invs.remove(k);
                        }
                        if emitted.slot == S::LoopExitCondition {
                            self.armed_exit_cond = false;
                        }
                    }
                }
                let mut node = None;
                let mut lowering_node = None;
                let mut subject_fn = None;
                // Rule (construction-exact): while armed, an assume whose
                // expression is the *same allocation* (`Arc::ptr_eq`) as a
                // recorded entry-check expression is that clause's exit
                // assume: `loop_to_stmts` clones one Arc into both
                // positions, so pointer identity distinguishes even two
                // syntactically identical invariant clauses. Runs before any
                // shape consideration and may override a shape-tier bucket;
                // a merely structurally-equal expression stays put.
                // The positional machine is a fallback for records without
                // exact emission-slot metadata. Running it after an exact
                // match can misclassify a negated final invariant as the
                // loop's negated exit condition.
                if emitted.is_none() {
                    if let Some(k) = self
                        .armed_exit_invs
                        .iter()
                        .position(|(e, _)| std::sync::Arc::ptr_eq(e, expr))
                    {
                        let (_, clause_span) = self.armed_exit_invs.remove(k);
                        class = Classification {
                            origin: record::Origin {
                                kind: record::OriginKind::Source,
                                detail: "loop_invariant".to_string(),
                            },
                            role: Some(EmissionRole::LoopInvariant { point: LoopPoint::Exit }),
                            rule: rules::R_LOOP_EXIT_INV,
                        };
                        span = Some(clause_span);
                    } else if self.armed_exit_cond
                        && self.armed_exit_invs.is_empty()
                        && matches!(&**expr, air::ast::ExprX::Unary(air::ast::UnaryOp::Not, _))
                        && self
                            .lowering(stmt)
                            .map(|provenance| provenance.emitted_at == LoweringSite::Loop)
                            .unwrap_or(true)
                    {
                        // All exit invariants matched; the lowering emits the
                        // negated loop condition next. One per arm.
                        self.armed_exit_cond = false;
                        class = Classification {
                            origin: record::Origin {
                                kind: record::OriginKind::Source,
                                detail: "loop_exit_condition".to_string(),
                            },
                            role: Some(EmissionRole::LoopExitCondition),
                            rule: rules::R_LOOP_EXIT_COND,
                        };
                    }
                }
                // Rule: an assume directly following an assert of the same
                // formula is the asserted proposition.
                let mut asserted_pair: Option<(usize, String)> = None;
                if classify::is_unresolved(&class) {
                    if let Some((assert_expr, assert_span, assert_index, assert_path)) =
                        &self.last_assert
                    {
                        if classify::exprs_equal(assert_expr, expr) {
                            // The role follows the paired check: a user
                            // assertion exports its proposition; a generated
                            // check (overflow, division, place requirement)
                            // re-assumes a checked condition.
                            let user_assertion = matches!(
                                self.occurrences[*assert_index].emission,
                                Some(EmissionRole::Assertion { point: AssertionPoint::Check })
                            );
                            class = Classification {
                                origin: record::Origin {
                                    kind: record::OriginKind::Derived,
                                    detail: "asserted_proposition".to_string(),
                                },
                                role: Some(if user_assertion {
                                    EmissionRole::Assertion { point: AssertionPoint::Establish }
                                } else {
                                    EmissionRole::Assumed {
                                        intent: record::AssumeIntent::CheckedCondition,
                                    }
                                }),
                                rule: rules::R_ASSERTED_PROP,
                            };
                            span = assert_span.clone();
                            asserted_pair = Some((*assert_index, assert_path.clone()));
                        }
                    }
                }
                if let Some(exact) = self.exact_lowering(stmt) {
                    if span.is_none() {
                        span = exact.span.clone();
                    }
                    node = exact.node.clone();
                    lowering_node = exact.node;
                    subject_fn = exact.subject_fn;
                    if classify::is_unresolved(&class) {
                        class = Classification {
                            origin: exact.origin,
                            role: Some(exact.role),
                            rule: rules::R_EXACT_LOWERING,
                        };
                    }
                }
                let shape = if classify::is_unresolved(&class) {
                    Some(classify::shape(expr))
                } else {
                    None
                };
                let occurrence_index = self.occurrences.len();
                self.sites.push(QuerySiteId::Statement(self.path.join(".")));
                self.occurrences.push(Occurrence {
                    path: self.path.join("."),
                    role: Role::Premise,
                    carrier: record::Carrier::Assume,
                    origin: class.origin,
                    emission: class.role,
                    rule: if class.rule.is_empty() { None } else { Some(class.rule.to_string()) },
                    join_rule: None,
                    span,
                    assert_id: None,
                    shape,
                    label: None,
                    node,
                    artifact: None,
                    sig: Some(classify::air_sig(expr)),
                    emitted,
                    lowering_node,
                    subject_fn,
                });
                if let Some((assert_index, assert_path)) = asserted_pair {
                    self.assert_pairs.push((
                        assert_index,
                        occurrence_index,
                        assert_path,
                        self.occurrences[occurrence_index].path.clone(),
                    ));
                }
                // Exported forall conclusion: exact statement-path match
                // against a pending assert-forall region.
                if self.occurrences[occurrence_index].origin.detail == "sst:AssertForallEnsures" {
                    let path = self.path.join(".");
                    if let Some(position) =
                        self.pending_forall.iter().position(|(_, _, export)| *export == path)
                    {
                        let (goal, hypothesis, _) = self.pending_forall.remove(position);
                        self.forall_pairs.push((hypothesis, goal, occurrence_index));
                    }
                }
                self.last_assert = None;
            }
            StmtX::Assert(assert_id, msg, _filter, expr) => {
                if self.require_lowering_provenance && self.lowering(stmt).is_none() {
                    self.missing_lowering_sites.push(self.path.join("."));
                }
                let emitted = self.emitted_clause(stmt);
                let (mut class, span) = match CoverageProducer::downcast_message(msg) {
                    Some(m) => (
                        classify::classify_obligation_note(&m.note),
                        m.spans.first().map(|s| s.as_string.clone()),
                    ),
                    None => (
                        Classification {
                            origin: record::Origin {
                                kind: record::OriginKind::Unresolved,
                                detail: "obligation_message_opaque".to_string(),
                            },
                            role: None,
                            rule: "",
                        },
                        None,
                    ),
                };
                if class.origin.detail == "requires_of_callee" {
                    if let Some(callee) = classify::callee_of_requires(expr) {
                        class.origin.detail = format!("requires_of:{}", callee);
                        class.role = Some(EmissionRole::CallPrecondition { callee: Some(callee) });
                        class = class.cite(rules::R_CALLEE_REQ);
                    }
                }
                // Bit-vector queries carry no diagnostic constant, only the slot
                // and declaring clause ordinal the lowering recorded.
                let mut span = span;
                if let Some(emitted) = emitted {
                    use record::EmissionSlot as S;
                    match emitted.slot {
                        S::BitVectorFunctionEnsures => {
                            class = Classification {
                                origin: record::Origin {
                                    kind: record::OriginKind::Source,
                                    detail: "ensures".to_string(),
                                },
                                role: Some(emitted.slot.role()),
                                rule: rules::R_EMITTED_SLOT,
                            };
                            if let Some(clause) = emitted.clause {
                                span = self.ens_spans.get(clause).cloned().or(span);
                            }
                        }
                        S::BitVectorAssertQueryEnsures => {
                            class = Classification {
                                origin: record::Origin {
                                    kind: record::OriginKind::Source,
                                    detail: "lemma_goal".to_string(),
                                },
                                role: Some(emitted.slot.role()),
                                rule: rules::R_EMITTED_SLOT,
                            };
                            if let Some(clause) = emitted.clause {
                                span = self
                                    .lemma_clauses
                                    .get(&self.query_span)
                                    .and_then(|(_, ens)| ens.get(clause))
                                    .cloned()
                                    .or(span);
                            }
                        }
                        _ => {}
                    }
                }
                let mut shape = if classify::is_unresolved(&class) {
                    Some(classify::shape(expr))
                } else {
                    None
                };
                let exact = self.exact_lowering(stmt);
                let span = span.or_else(|| exact.as_ref().and_then(|exact| exact.span.clone()));
                let lowering_node = exact.as_ref().and_then(|exact| exact.node.clone());
                if classify::is_unresolved(&class) {
                    if let Some(exact) = &exact {
                        class = Classification {
                            origin: exact.origin.clone(),
                            role: Some(exact.role.clone()),
                            rule: rules::R_EXACT_LOWERING,
                        };
                        shape = None;
                    }
                }
                self.sites.push(QuerySiteId::Statement(self.path.join(".")));
                self.occurrences.push(Occurrence {
                    path: self.path.join("."),
                    role: Role::Obligation,
                    carrier: record::Carrier::Assert,
                    origin: class.origin,
                    emission: class.role,
                    rule: if class.rule.is_empty() { None } else { Some(class.rule.to_string()) },
                    join_rule: None,
                    span,
                    assert_id: assert_id.as_ref().map(|id| format!("{:?}", id)),
                    shape,
                    label: None,
                    node: exact.and_then(|exact| exact.node),
                    artifact: None,
                    sig: None,
                    emitted,
                    lowering_node,
                    subject_fn: None,
                });
                self.last_assert = Some((
                    expr.clone(),
                    self.occurrences.last().unwrap().span.clone(),
                    self.occurrences.len() - 1,
                    self.occurrences.last().unwrap().path.clone(),
                ));
                // Loop-exit protocol: entry checks feed the arm; any assert
                // ends the exit-assume region.
                {
                    let o = self.occurrences.last().unwrap();
                    if o.emission
                        == Some(EmissionRole::LoopInvariant { point: LoopPoint::Establish })
                    {
                        if let Some(s) = &o.span {
                            self.recent_establish.push((expr.clone(), s.clone()));
                        }
                    } else {
                        self.recent_establish.clear();
                    }
                }
                self.armed_exit_invs.clear();
                self.armed_exit_cond = false;
            }
            StmtX::Block(stmts) => {
                for (i, s) in stmts.iter().enumerate() {
                    self.path.push(format!("b{}", i));
                    self.walk(s);
                    self.path.pop();
                }
                self.last_assert = None;
            }
            StmtX::Switch(stmts) => {
                self.join_stmts.insert(self.path.join("."), stmt.clone());
                for (i, s) in stmts.iter().enumerate() {
                    self.path.push(format!("s{}", i));
                    let arm_first = self.occurrences.len();
                    self.walk(s);
                    // Rule: the first premise of a switch arm is that arm's
                    // branch condition.
                    if let Some(first) = self.occurrences.get_mut(arm_first) {
                        if first.role == Role::Premise
                            && (first.origin.kind == record::OriginKind::Unresolved
                                || (first.rule.as_deref() == Some(rules::R_EXACT_LOWERING)
                                    && first.origin.detail == "lowering:If"))
                        {
                            first.rule = Some(rules::R_BRANCH_COND.to_string());
                            first.origin = record::Origin {
                                kind: record::OriginKind::Derived,
                                detail: "branch_condition".to_string(),
                            };
                            first.emission = Some(EmissionRole::BranchCondition { arm: i as u32 });
                            first.shape = None;
                        }
                    }
                    self.path.pop();
                }
                self.last_assert = None;
            }
            StmtX::DeadEnd(s) => {
                // An assert-forall proof region: the lowering emits
                //   DeadEnd { assume AssertForallRequire; body; assert goal }
                //   assume AssertForallEnsures            <- next sibling
                // so the region and its export are identified structurally,
                // by exact statement path, and nest correctly.
                let region_start = self.occurrences.len();
                let export_path = match self.path.last().and_then(|last| {
                    last.strip_prefix('b').and_then(|index| index.parse::<usize>().ok())
                }) {
                    Some(index) => {
                        let mut sibling = self.path.clone();
                        let last = sibling.len() - 1;
                        sibling[last] = format!("b{}", index + 1);
                        Some(sibling.join("."))
                    }
                    None => None,
                };
                self.path.push("d".to_string());
                self.walk(s);
                self.path.pop();
                if let Some(export_path) = export_path {
                    let region = &self.occurrences[region_start..];
                    let hypothesis = region.iter().position(|occurrence| {
                        occurrence.role == Role::Premise
                            && occurrence.origin.detail == "sst:AssertForallRequire"
                    });
                    let goal =
                        region.iter().rposition(|occurrence| occurrence.role == Role::Obligation);
                    // Guarded: the region must open with the forall hypothesis
                    // and contain at least one obligation to discharge.
                    if let (Some(hypothesis), Some(goal)) = (hypothesis, goal) {
                        if region[..hypothesis]
                            .iter()
                            .all(|occurrence| occurrence.role == Role::Premise)
                        {
                            self.pending_forall.push((
                                region_start + goal,
                                region_start + hypothesis,
                                export_path,
                            ));
                        }
                    }
                }
                self.last_assert = None;
            }
            StmtX::Breakable(_label, s) => {
                // Non-isolated loop bodies are `breakable(break_label%<id>) {
                // havoc…; assume typ_inv…; assume invs…; body; assert invs;
                // assume false }`. Every invariant position inside is
                // attributed by its recorded emission slot.
                self.join_stmts.insert(self.path.join("."), stmt.clone());
                self.path.push("k".to_string());
                self.walk(s);
                self.path.pop();
                self.last_assert = None;
            }
            StmtX::Snapshot(id) => {
                // `Snapshot(snap%LOOP)` is emitted by the loop-isolation
                // lowering immediately before the exit-side assumes
                // (sst_to_air::loop_to_stmts). Arm the exit protocol with the
                // entry-check expressions of the loop just checked.
                if **id == *vir::def::snapshot_ident(vir::def::SNAPSHOT_LOOP) {
                    self.armed_exit_invs = std::mem::take(&mut self.recent_establish);
                    self.armed_exit_cond = true;
                }
            }
            StmtX::Assign(_, _) => {
                // A mutating assignment. Its equality is synthesized by the SSA
                // pass after this point; the shadow clone guards the statement
                // so that equality becomes a labelled premise. Provenance comes
                // from the lowering sidecar, which records Assign statements.
                if self.require_lowering_provenance && self.lowering(stmt).is_none() {
                    self.missing_lowering_sites.push(self.path.join("."));
                }
                let exact = self.exact_lowering(stmt);
                let (span, node, lowering_node) = match &exact {
                    Some(exact) => (exact.span.clone(), exact.node.clone(), exact.node.clone()),
                    None => (None, None, None),
                };
                self.sites.push(QuerySiteId::Statement(self.path.join(".")));
                self.occurrences.push(Occurrence {
                    path: self.path.join("."),
                    role: Role::Premise,
                    carrier: record::Carrier::Assign,
                    origin: record::Origin {
                        kind: record::OriginKind::Derived,
                        detail: "sst:AssignUpdate".to_string(),
                    },
                    emission: Some(EmissionRole::MutationEquality),
                    rule: Some(rules::R_EXACT_LOWERING.to_string()),
                    join_rule: None,
                    span,
                    assert_id: None,
                    shape: None,
                    label: None,
                    node,
                    artifact: None,
                    sig: None,
                    emitted: None,
                    lowering_node,
                    subject_fn: None,
                });
                self.last_assert = None;
            }
            StmtX::Break(..) => {
                self.join_stmts.insert(self.path.join("."), stmt.clone());
            }
            StmtX::Havoc(..) => {}
        }
    }

    /// Occurrences for the reconciliation equalities the SSA pass generates,
    /// one per `Reconciliation` site the shadow minted from the pass's trace.
    /// Placement is the join statement's exact lowering (`If`, `Loop`,
    /// `BreakOrContinue` frames); without it the row is `Unresolved`.
    fn walk_reconciliations(&mut self, sites: &BTreeMap<QuerySiteId, SolverToken>) {
        for site in sites.keys() {
            let QuerySiteId::Reconciliation { at, join, var, from, to } = site else {
                continue;
            };
            let exact = self.join_stmts.get(at).cloned().and_then(|s| self.exact_lowering(&s));
            let detail = format!("ssa:reconcile {var}@{from}->@{to}");
            let (origin, rule, span, node) = match &exact {
                Some(exact) => (
                    record::Origin { kind: record::OriginKind::Generated, detail },
                    Some(rules::R_SSA_TRACE.to_string()),
                    exact.span.clone(),
                    exact.node.clone(),
                ),
                None => (
                    record::Origin {
                        kind: record::OriginKind::Unresolved,
                        detail: format!("{detail}: join without lowering provenance"),
                    },
                    None,
                    None,
                    None,
                ),
            };
            let join = match join {
                SsaJoin::SwitchArm(arm) => record::SsaJoinKind::SwitchArm { arm: *arm },
                SsaJoin::Fallthrough => record::SsaJoinKind::Fallthrough,
                SsaJoin::Break => record::SsaJoinKind::Break,
            };
            self.sites.push(site.clone());
            self.occurrences.push(Occurrence {
                path: at.clone(),
                role: Role::Premise,
                carrier: record::Carrier::SsaReconciliation,
                origin,
                emission: Some(EmissionRole::SsaReconciliation { join }),
                rule,
                join_rule: None,
                span,
                assert_id: None,
                shape: None,
                label: None,
                node: node.clone(),
                artifact: None,
                sig: None,
                emitted: None,
                lowering_node: node,
                subject_fn: None,
            });
        }
    }

    fn walk_local_axioms(&mut self, local: &air::ast::Decls) {
        let mut axiom_ordinal = 0u32;
        for decl in local.iter() {
            if let DeclX::Axiom(axiom) = &**decl {
                let class = classify::classify_premise(&axiom.expr);
                let mut origin = class.origin;
                let mut role = class.role;
                let mut rule = if class.rule.is_empty() { None } else { Some(class.rule) };
                let mut span = None;
                // Exact provenance from the declaration-level sidecar. The
                // lowering recorded which construction emitted this Decl, so
                // origin, protocol site and source position follow from
                // identity; the vocabulary classification above is retained
                // only where the sidecar has no entry.
                if let Some(site) = self.local_axioms.get(&(Arc::as_ptr(decl) as usize)) {
                    let generated = |detail: &str| record::Origin {
                        kind: record::OriginKind::Generated,
                        detail: detail.to_string(),
                    };
                    match site {
                        LocalAxiomSite::Requires { clause } => {
                            origin = record::Origin {
                                kind: record::OriginKind::Source,
                                detail: format!("requires[{clause}]"),
                            };
                            role = Some(EmissionRole::FunctionRequires { clause: *clause as u32 });
                            span = self.req_spans.get(*clause).cloned();
                        }
                        LocalAxiomSite::ParamTypeInvariant { param } => {
                            origin = generated("type_invariant");
                            role = Some(EmissionRole::TypeInvariant {
                                site: TypeInvariantSite::Parameter,
                            });
                            span = self.param_spans.get(*param).cloned();
                        }
                        LocalAxiomSite::TraitBound { .. } => {
                            if !origin.detail.starts_with("trait_bound") {
                                origin = generated("trait_bound");
                            }
                            role = Some(EmissionRole::TraitBound);
                            span = Some(self.query_span.clone());
                        }
                        LocalAxiomSite::Fuel => {
                            origin = generated("fuel");
                            role = Some(EmissionRole::Fuel { site: FuelSite::Function });
                            span = Some(self.query_span.clone());
                        }
                        LocalAxiomSite::LoopTypeInvariant { .. } => {
                            origin = generated("type_invariant");
                            role =
                                Some(EmissionRole::TypeInvariant { site: TypeInvariantSite::Loop });
                            span = match site {
                                LocalAxiomSite::LoopTypeInvariant { loop_id } => {
                                    self.loop_spans_by_id.get(loop_id).cloned()
                                }
                                _ => None,
                            };
                        }
                        LocalAxiomSite::AssertQueryTypeInvariant => {
                            origin = generated("type_invariant");
                            role = Some(EmissionRole::TypeInvariant {
                                site: TypeInvariantSite::AssertQuery,
                            });
                            span = Some(self.query_span.clone());
                        }
                        LocalAxiomSite::AssertQueryRequires { clause } => {
                            // `assert ... by(bit_vector)`: the requires are
                            // installed as axioms of the isolated query.
                            origin = record::Origin {
                                kind: record::OriginKind::Source,
                                detail: "sst:AssertQueryRequire".to_string(),
                            };
                            role = Some(EmissionRole::AssertQuery {
                                section: ContractSection::Requires,
                                point: AssertQueryPoint::Assume,
                            });
                            span = self
                                .lemma_clauses
                                .get(&self.query_span)
                                .and_then(|(req, _)| req.get(*clause))
                                .cloned();
                        }
                    }
                    rule = Some(rules::R_EMITTED_AXIOM);
                }
                let shape = if origin.kind == record::OriginKind::Unresolved {
                    Some(classify::shape(&axiom.expr))
                } else {
                    None
                };
                self.sites.push(QuerySiteId::LocalAxiom(axiom_ordinal));
                axiom_ordinal += 1;
                self.occurrences.push(Occurrence {
                    path: format!(
                        "local.{}",
                        axiom.named.as_ref().map(|n| n.to_string()).unwrap_or("_".to_string())
                    ),
                    role: Role::Premise,
                    carrier: record::Carrier::QueryLocalAxiom,
                    origin,
                    emission: role,
                    rule: rule.map(str::to_string),
                    join_rule: None,
                    span,
                    assert_id: None,
                    shape,
                    label: None,
                    node: None,
                    artifact: None,
                    sig: None,
                    // A Decl has no template slot; its identity is carried by
                    // `local_axioms` above and consumed here directly.
                    emitted: None,
                    lowering_node: None,
                    subject_fn: None,
                });
            }
        }
    }
}

impl VerificationObserver for CoverageProducer {
    fn on_context_installed(
        &mut self,
        solver: SolverContextId,
        solver_config: &SolverReplayConfig,
        reason: &ContextInstallReason,
        commands: &air::ast::Commands,
    ) {
        self.events.push(RawEvent::ContextInstalled(
            solver,
            solver_config.clone(),
            reason.clone(),
            commands.clone(),
        ));
    }

    fn on_query(
        &mut self,
        query_instance: Option<QueryInstanceId>,
        solver: SolverContextId,
        context: &CommandContext,
        solver_config: &SolverReplayConfig,
        lowering_provenance: &LoweringProvenance,
        command: &Command,
    ) {
        self.events.push(RawEvent::Query(
            query_instance,
            solver,
            solver_config.clone(),
            lowering_provenance.clone(),
            context.clone(),
            command.clone(),
        ));
    }

    fn on_query_result(
        &mut self,
        query_instance: Option<QueryInstanceId>,
        solver: SolverContextId,
        _context: &CommandContext,
        result: &ValidityResult,
    ) {
        let key = match result {
            ValidityResult::Valid(_) => "valid",
            ValidityResult::Invalid(..) => "invalid",
            ValidityResult::Canceled => "canceled",
            ValidityResult::TypeError(_) => "type_error",
            ValidityResult::UnexpectedOutput(_) => "unexpected_output",
        };
        self.events.push(RawEvent::QueryResult(query_instance, solver, key));
    }

    fn on_finish(&mut self) {
        // Post-verification processing: replay the snapshots in order
        // through the handlers, then run the shadow/emit pipeline.
        for ev in std::mem::take(&mut self.events) {
            match ev {
                RawEvent::SourceInventory(functions) => self.source_functions = functions,
                RawEvent::AirNames(names) => self.air_names.extend(names),
                RawEvent::FunctionSst(instance, f, ch) => {
                    self.handle_function_sst(instance, &f, &ch)
                }
                RawEvent::ContextInstalled(s, cfg, r, cmds) => {
                    self.handle_context_installed(s, &cfg, &r, &cmds)
                }
                RawEvent::Query(instance, s, cfg, provenance, ctx, cmd) => {
                    self.handle_query(instance, s, &cfg, &provenance, &ctx, &cmd)
                }
                RawEvent::QueryResult(instance, s, k) => self.handle_query_result(instance, s, k),
            }
        }
        self.handle_finish();
    }

    fn on_krate_pre_simplify(&mut self, krate: &Krate, crate_id: &vir::ast::CrateId) {
        // This callback sees the one complete source crate before
        // simplification rewrites contracts or creates helper functions.
        // `on_krate` is bucket-local and receives a pruned crate, so using it
        // for source inventory made the final artifact depend on serial vs.
        // parallel bucket completion order.
        let local_crate = Some(crate_id);
        let functions = krate
            .functions
            .iter()
            .map(|function| {
                let authored = !function.span.proof_coverage_generated;
                let mut ens_spans = function
                    .x
                    .ensure
                    .0
                    .iter()
                    .chain(function.x.ensure.1.iter())
                    .filter(|expr| !expr.span.proof_coverage_generated)
                    .map(|expr| expr.span.as_string.clone())
                    .collect::<Vec<_>>();
                if let Some(returns) = &function.x.returns {
                    if !returns.span.proof_coverage_generated {
                        let span = returns.span.as_string.clone();
                        if !ens_spans.contains(&span) {
                            ens_spans.push(span);
                        }
                    }
                }
                let fun = verus::fun_identity(&function.x.name);
                SourceFunctionInventory {
                    fun: fun.clone(),
                    authored,
                    source: Self::source_function(fun, function, local_crate),
                    req_spans: function
                        .x
                        .require
                        .iter()
                        .filter(|expr| !expr.span.proof_coverage_generated)
                        .map(|expr| expr.span.as_string.clone())
                        .collect(),
                    ens_spans,
                    dec_spans: function
                        .x
                        .decrease
                        .iter()
                        .filter(|expr| !expr.span.proof_coverage_generated)
                        .map(|expr| expr.span.as_string.clone())
                        .collect(),
                    param_spans: function
                        .x
                        .params
                        .iter()
                        .map(|param| param.span.as_string.clone())
                        .collect(),
                    refines: match &function.x.kind {
                        vir::ast::FunctionKind::TraitMethodImpl { method, .. } => {
                            Some(verus::fun_identity(method))
                        }
                        _ => None,
                    },
                    body_artifacts: function
                        .x
                        .body
                        .as_ref()
                        .filter(|_| authored)
                        .map(|body| {
                            Self::source_body_inventory(
                                &verus::fun_identity(&function.x.name),
                                body,
                                function.x.ens_has_return,
                            )
                        })
                        .unwrap_or_default(),
                }
            })
            .collect();
        self.events.push(RawEvent::SourceInventory(functions));
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn on_krate(&mut self, krate: &Krate, name_ctxt: &vir::def::NameCtxt) {
        // Bucket-local and pruned, so the table is accumulated across
        // buckets; the pairing itself is a pure function of the name.
        let names = krate
            .functions
            .iter()
            .map(|f| (name_ctxt.fun_to_string(&f.x.name), verus::fun_identity(&f.x.name)))
            .collect();
        self.events.push(RawEvent::AirNames(names));
    }

    fn on_function_sst(
        &mut self,
        query_instance: QueryInstanceId,
        function: &FunctionSst,
        check: &Arc<FuncCheckSst>,
    ) {
        self.events.push(RawEvent::FunctionSst(query_instance, function.clone(), check.clone()));
    }
}

impl CoverageProducer {
    fn handle_function_sst(
        &mut self,
        query_instance: QueryInstanceId,
        function: &FunctionSst,
        check: &Arc<FuncCheckSst>,
    ) {
        let info = Self::collect_sst(check);
        let fun = verus::fun_identity(&function.x.name);
        let mut source_by_id: BTreeMap<vir::messages::AstId, Vec<String>> = BTreeMap::new();
        let mut loop_source_by_id: BTreeMap<vir::messages::AstId, Vec<String>> = BTreeMap::new();
        let mut implicit_return_artifact = None;
        if let Some(source) = self.source_functions.iter().find(|source| source.fun == fun) {
            for artifact in &source.body_artifacts {
                if artifact.kind == record::ArtifactKind::ReturnBinding
                    && artifact.id == format!("{fun}#return.src0")
                {
                    implicit_return_artifact = Some(artifact.id.clone());
                }
                for source_id in &artifact.source_ids {
                    source_by_id.entry(*source_id).or_default().push(artifact.id.clone());
                    if artifact.kind == record::ArtifactKind::LoopInvariantClause {
                        loop_source_by_id.entry(*source_id).or_default().push(artifact.id.clone());
                    }
                }
            }
        }
        let projected_sites = info
            .sites
            .iter()
            .map(|site| {
                let mut artifacts = site
                    .source_ids
                    .iter()
                    .flat_map(|id| source_by_id.get(id).into_iter().flatten().cloned())
                    .collect::<Vec<_>>();
                if info.implicit_return_nodes.contains(&site.node) {
                    if let Some(artifact) = &implicit_return_artifact {
                        artifacts.push(artifact.clone());
                    }
                }
                artifacts.sort();
                artifacts.dedup();
                (site.node.clone(), artifacts)
            })
            .collect::<Vec<_>>();
        let projected_loop_clauses = info
            .loop_source_ids
            .iter()
            .flat_map(|(loop_id, clauses)| {
                clauses.iter().enumerate().filter_map(|(clause, source_id)| {
                    let candidates = loop_source_by_id.get(source_id)?;
                    match candidates.as_slice() {
                        [artifact] => Some((*loop_id, clause, artifact.clone())),
                        _ => None,
                    }
                })
            })
            .collect::<Vec<_>>();
        let mut sites = BTreeMap::new();
        let mut duplicate_sites = BTreeSet::new();
        for site in &info.sites {
            if duplicate_sites.contains(&site.statement) {
                continue;
            }
            if sites.insert(site.statement, site.clone()).is_some() {
                sites.remove(&site.statement);
                duplicate_sites.insert(site.statement);
            }
        }
        self.sst_sites_by_query_instance.insert(query_instance, sites);
        let mut record = FunctionRecord {
            variant: String::new(),
            fun,
            cfg: info.cfg,
            invariant_block_members: info.invariant_block_members,
            resolved_calls: info
                .call_sites
                .iter()
                .filter_map(|cs| cs.resolved_callee.clone().map(|r| (cs.node.clone(), r)))
                .collect(),
            call_sites: info
                .call_sites
                .into_iter()
                .map(|cs| (cs.node, cs.span, cs.callee))
                .collect(),
            sst_assumes: info.assumes,
            lemmas: info.lemmas,
            recursive_calls: info.recursive_calls,
            ens_spans: check
                .post_condition
                .ens_exps
                .iter()
                .map(|e| e.span.as_string.clone())
                .collect(),
            req_spans: check.reqs.iter().map(|e| e.span.as_string.clone()).collect(),
            param_spans: function.x.pars.iter().map(|p| p.span.as_string.clone()).collect(),
            branches: info.branches,
            synthetic_bindings: info.synthetic_bindings,
            loops: info.loops,
        };
        let encoded =
            serde_json::to_vec(&record).expect("FunctionRecord serialization must succeed");
        let digest = Sha256::digest(encoded);
        record.variant = format!(
            "pc_fv%{}",
            digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>()
        );
        for (node, artifacts) in projected_sites {
            if !artifacts.is_empty() {
                self.source_artifacts_by_site.insert((record.variant.clone(), node), artifacts);
            }
        }
        for (loop_id, clause, artifact) in projected_loop_clauses {
            self.source_loop_clauses.insert((record.variant.clone(), loop_id, clause), artifact);
        }
        self.function_variant_by_query_instance.insert(query_instance, record.variant.clone());
        self.last_batch_by_query_instance.remove(&query_instance);
        self.functions.push(record);
    }

    fn handle_context_installed(
        &mut self,
        solver: SolverContextId,
        solver_config: &SolverReplayConfig,
        reason: &ContextInstallReason,
        commands: &Commands,
    ) {
        *self.ambient_batches.entry(solver).or_insert(0) += 1;
        // Record named ambient axioms with their owner. Function-owned
        // unnamed axioms receive stable names only in the shadow clone;
        // setup/prelude axioms remain background β. This preserves ambient
        // evidence without enabling canonical axiom-usage mode.
        let (op, owner, function_owned) = match reason {
            ContextInstallReason::FunctionContext { op, owner } => {
                (op.clone(), owner.clone(), true)
            }
            ContextInstallReason::Setup(title) => ("Setup".to_string(), title.clone(), false),
        };
        let mut shadow_commands: Vec<Command> = Vec::with_capacity(commands.len());
        let mut axiom_ordinal = 0usize;
        for command in commands.iter() {
            let mut shadow_command = command.clone();
            if let CommandX::Global(decl) = &**command {
                if let DeclX::Axiom(Axiom { named, expr }) = &**decl {
                    let ordinal = axiom_ordinal;
                    axiom_ordinal += 1;
                    let label = if let Some(label) = named {
                        Some(label.to_string())
                    } else if function_owned && !owner.is_empty() {
                        let (label, fingerprint) = Self::ambient_label(&op, &owner, ordinal, expr);
                        match self.ambient_fingerprints.get(&label) {
                            Some(previous) if previous != &fingerprint => {
                                eprintln!(
                                    "proof-coverage: warning: synthetic ambient-label collision for \
                                     owner {owner}; leaving this axiom in background"
                                );
                                None
                            }
                            _ => {
                                self.ambient_fingerprints.insert(label.clone(), fingerprint);
                                let shadow_decl = Arc::new(DeclX::Axiom(Axiom {
                                    named: Some(Arc::new(label.clone())),
                                    expr: expr.clone(),
                                }));
                                shadow_command = Arc::new(CommandX::Global(shadow_decl));
                                Some(label)
                            }
                        }
                    } else {
                        None
                    };

                    match label {
                        Some(label) => {
                            let entry = self.ambients.entry(label.clone()).or_insert_with(|| {
                                AmbientRecord {
                                    label,
                                    op: op.clone(),
                                    owner: owner.clone(),
                                    solver_contexts: Vec::new(),
                                }
                            });
                            if !entry.solver_contexts.contains(&solver) {
                                entry.solver_contexts.push(solver);
                            }
                        }
                        None => {
                            *self.background_axioms.entry(solver).or_insert(0) += 1;
                        }
                    }
                }
            }
            shadow_commands.push(shadow_command);
        }
        self.shadow_events.entry(solver).or_default().push(shadow::ShadowEvent::Ambient {
            solver_config: solver_config.clone(),
            commands: Arc::new(shadow_commands),
        });
    }

    fn handle_query(
        &mut self,
        query_instance: Option<QueryInstanceId>,
        solver: SolverContextId,
        solver_config: &SolverReplayConfig,
        lowering_provenance: &LoweringProvenance,
        context: &CommandContext,
        command: &Command,
    ) {
        let CommandX::CheckValid(query) = &**command else {
            return;
        };
        let function_variant = query_instance
            .and_then(|instance| self.function_variant_by_query_instance.get(&instance))
            .cloned();
        let function_idx = function_variant
            .as_ref()
            .and_then(|variant| self.functions.iter().position(|f| &f.variant == variant));
        let exact_sst_sites = lowering_provenance.lowered_body.as_ref().map(|body| {
            let mut sites = BTreeMap::new();
            let mut duplicates = BTreeSet::new();
            for site in cfg::sites_for_body(body) {
                if duplicates.contains(&site.statement) {
                    continue;
                }
                if sites.insert(site.statement, site.clone()).is_some() {
                    sites.remove(&site.statement);
                    duplicates.insert(site.statement);
                }
            }
            sites
        });
        let sst_sites = exact_sst_sites.as_ref().or_else(|| {
            query_instance.and_then(|instance| self.sst_sites_by_query_instance.get(&instance))
        });
        let loop_clause_spans: BTreeMap<u64, Vec<String>> = function_idx
            .map(|f| {
                self.functions[f]
                    .loops
                    .iter()
                    .map(|l| (l.id, l.invs.iter().map(|(s, _, _)| s.clone()).collect()))
                    .collect()
            })
            .unwrap_or_default();

        let fun_name = verus::fun_identity(&context.fun);
        let source_inventory = self.source_functions.iter().find(|f| f.fun == fun_name);
        let mut walk = QueryWalk {
            occurrences: Vec::new(),
            sites: Vec::new(),
            path: Vec::new(),
            lowering_provenance: &lowering_provenance.statements,
            sst_sites,
            require_lowering_provenance: lowering_provenance.lowered_body.is_some(),
            missing_lowering_sites: Vec::new(),
            join_stmts: BTreeMap::new(),
            last_assert: None,
            assert_pairs: Vec::new(),
            pending_forall: Vec::new(),
            forall_pairs: Vec::new(),
            armed_exit_invs: Vec::new(),
            recent_establish: Vec::new(),
            armed_exit_cond: false,
            emission_slots: &lowering_provenance.slots,
            loop_clause_spans,
            local_axioms: &lowering_provenance.local_axioms,
            // Clause spans come from the pre-simplified source inventory: they
            // are the clauses as written, which is what the artifacts carry.
            // The SST's clause spans can differ (a `by(bit_vector)` body has
            // its spec-function calls inlined, moving the span into the spec
            // function). The SST record is the fallback for a function the
            // inventory does not list.
            // A trait method implementation declares no clauses of its own
            // (they are on the trait), so its inventory lists are empty while
            // the SST carries the inherited clauses: the choice is per clause.
            req_spans: Self::clause_spans(
                source_inventory.map(|f| f.req_spans.as_slice()),
                function_idx.map(|f| self.functions[f].req_spans.as_slice()),
            ),
            ens_spans: Self::clause_spans(
                source_inventory.map(|f| f.ens_spans.as_slice()),
                function_idx.map(|f| self.functions[f].ens_spans.as_slice()),
            ),
            param_spans: function_idx
                .map(|f| self.functions[f].param_spans.clone())
                .or_else(|| source_inventory.map(|f| f.param_spans.clone()))
                .unwrap_or_default(),
            lemma_clauses: function_idx
                .map(|f| {
                    self.functions[f]
                        .lemmas
                        .iter()
                        .map(|l| (l.span.clone(), (l.requires.clone(), l.ensures.clone())))
                        .collect()
                })
                .unwrap_or_default(),
            loop_spans_by_id: function_idx
                .map(|f| self.functions[f].loops.iter().map(|l| (l.id, l.span.clone())).collect())
                .unwrap_or_default(),
            query_span: context.span.as_string.clone(),
        };
        walk.walk_local_axioms(&query.local);
        walk.walk(&query.assertion);

        // Instrument a clone for the shadow run and attach activation labels
        // through an exact typed structural-site join. Any disagreement fails
        // closed: the query is recorded as unmeasured and no core is emitted.
        let instrumented = shadow::instrument_query(self.next_query_id, query);
        // The SSA reconciliation sites exist only in the instrumenter's trace;
        // their occurrences are placed at the join statements walked above.
        walk.walk_reconciliations(&instrumented.site_tokens);
        let mut occurrences = walk.occurrences;
        let occurrence_sites = walk.sites;
        let missing_lowering_sites = walk.missing_lowering_sites;
        let walk_assert_pairs = walk.assert_pairs;
        let walk_forall_pairs = walk.forall_pairs;
        let mut identity_error = instrumented.identity_error.clone();
        if !missing_lowering_sites.is_empty() {
            identity_error = Some(format!(
                "lowering sidecar omitted structured AIR sites: {:?}",
                missing_lowering_sites
            ));
        }
        if occurrence_sites.len() != occurrences.len() {
            identity_error = Some(format!(
                "occurrence/site count mismatch: {} occurrences, {} sites",
                occurrences.len(),
                occurrence_sites.len()
            ));
        }
        let mut joined_sites = BTreeSet::new();
        for (site, occurrence) in occurrence_sites.iter().zip(occurrences.iter_mut()) {
            if !joined_sites.insert(site.clone()) {
                identity_error = Some(format!("duplicate producer occurrence site: {:?}", site));
                continue;
            }
            match instrumented.site_tokens.get(site) {
                Some(token) => occurrence.label = Some(token.as_str().to_string()),
                None => {
                    identity_error =
                        Some(format!("instrumenter omitted occurrence site: {:?}", site));
                }
            }
        }
        if joined_sites.len() != instrumented.site_tokens.len() {
            let extras: Vec<_> = instrumented
                .site_tokens
                .keys()
                .filter(|site| !joined_sites.contains(*site))
                .collect();
            if !extras.is_empty() {
                identity_error =
                    Some(format!("instrumenter emitted unknown occurrence sites: {:?}", extras));
            }
        }
        if let Some(error) = &identity_error {
            eprintln!(
                "proof-coverage: instrumentation identity mismatch for {}: {}",
                context.desc, error
            );
        }
        // Focused queries: one per terminal of every obligation, sharing the
        // batch query's label space plus one fresh target activation each.
        let focused = shadow::focused_queries(self.next_query_id, &instrumented);

        if identity_error.is_none() {
            self.shadow_events.entry(solver).or_default().push(shadow::ShadowEvent::Query {
                solver_config: solver_config.clone(),
                record_idx: self.queries.len(),
                command: Arc::new(air::ast::CommandX::CheckValid(instrumented.query)),
                ssa_plan: instrumented.ssa_plan,
            });
        }

        let batch_id = self.next_query_id;
        let fun = fun_name;
        let batch_record_idx = self.queries.len();
        self.queries.push(QueryRecord {
            id: batch_id,
            family: record::QueryFamily::Batch,
            parent: None,
            parent_obligation_label: None,
            target_label: None,
            terminal_path: None,
            function_variant: function_variant.clone(),
            solver_context: solver,
            solver_config: Self::solver_config_record(solver_config),
            fun: fun.clone(),
            desc: context.desc.clone(),
            span: context.span.as_string.clone(),
            ambient_batches: self.ambient_batches.get(&solver).copied().unwrap_or(0),
            available: Vec::new(),
            occurrences,
            results: Vec::new(),
            shadow_result: identity_error
                .as_ref()
                .map(|_| "instrumentation_identity_mismatch".to_string()),
            evidence_backend: None,
            core: None,
        });
        if let Some(query_instance) = query_instance {
            self.last_batch_by_query_instance.insert(query_instance, batch_record_idx);
        }
        if !walk_assert_pairs.is_empty() {
            self.assert_pairs.insert(batch_record_idx, walk_assert_pairs);
        }
        if !walk_forall_pairs.is_empty() {
            self.forall_pairs.insert(batch_record_idx, walk_forall_pairs);
        }
        self.next_query_id += 1;

        for fq in focused {
            if identity_error.is_none() {
                self.shadow_events.entry(solver).or_default().push(shadow::ShadowEvent::Query {
                    solver_config: solver_config.clone(),
                    record_idx: self.queries.len(),
                    command: Arc::new(air::ast::CommandX::CheckValid(fq.query)),
                    ssa_plan: fq.ssa_plan,
                });
            }
            self.queries.push(QueryRecord {
                id: self.next_query_id,
                family: record::QueryFamily::Focused,
                parent: Some(batch_id),
                parent_obligation_label: Some(fq.parent_label),
                target_label: Some(fq.target_label),
                terminal_path: Some(fq.terminal_path),
                function_variant: function_variant.clone(),
                solver_context: solver,
                solver_config: Self::solver_config_record(solver_config),
                fun: fun.clone(),
                desc: context.desc.clone(),
                span: context.span.as_string.clone(),
                ambient_batches: self.ambient_batches.get(&solver).copied().unwrap_or(0),
                available: fq.available,
                occurrences: Vec::new(),
                results: Vec::new(),
                shadow_result: identity_error
                    .as_ref()
                    .map(|_| "instrumentation_identity_mismatch".to_string()),
                evidence_backend: None,
                core: None,
            });
            self.next_query_id += 1;
        }
    }

    fn handle_query_result(
        &mut self,
        query_instance: Option<QueryInstanceId>,
        solver: SolverContextId,
        key: &'static str,
    ) {
        *self.results.entry(key.to_string()).or_insert(0) += 1;
        // handle_query appends focused shadow-query records immediately after
        // their canonical batch record.  Canonical result callbacks belong to
        // that batch, never to one of those synthetic focused children.
        if let Some(index) =
            query_instance.and_then(|instance| self.last_batch_by_query_instance.get(&instance))
        {
            if let Some(q) = self.queries.get_mut(*index) {
                debug_assert_eq!(q.solver_context, solver);
                debug_assert_eq!(q.family, record::QueryFamily::Batch);
                q.results.push(key.to_string());
            }
        }
    }

    fn handle_finish(&mut self) {
        // A canonically unsuccessful batch has no successful obligation
        // discharge to explain. Do not spend shadow-solver work on it or on
        // its focused children; retain both in the record as explicit
        // not-applicable/unmeasured boundaries. Other successful batches in
        // the same (possibly expected-failure) source file remain measurable.
        let mut unsuccessful_batches: BTreeMap<u64, String> = BTreeMap::new();
        for q in self.queries.iter_mut().filter(|q| q.family == record::QueryFamily::Batch) {
            if let Some(reason) = Self::canonical_shadow_skip_reason(&q.results) {
                q.shadow_result = Some(reason.to_string());
                unsuccessful_batches.insert(q.id, reason.to_string());
            }
        }
        let mut canonical_unmeasured = unsuccessful_batches.len() as u64;
        for q in self.queries.iter_mut().filter(|q| q.family == record::QueryFamily::Focused) {
            if let Some(reason) =
                q.parent.and_then(|parent| unsuccessful_batches.get(&parent)).cloned()
            {
                q.shadow_result = Some(reason);
                canonical_unmeasured += 1;
            }
        }
        if canonical_unmeasured > 0 {
            eprintln!(
                "proof-coverage: {} batch/focused measurements not requested because their \
                 canonical batch was not successfully discharged",
                canonical_unmeasured
            );
        }

        // Shadow-solve every buffered context; failures leave queries
        // unmeasured (missing core), never guessed.
        let trace_shadow = std::env::var_os("VERUS_PROOF_COVERAGE_TRACE_SHADOW").is_some();
        let minimize_cores = std::env::var_os(MINIMIZE_CORES_ENV).is_some();
        let shadow_log_dir =
            std::env::var_os("VERUS_PROOF_COVERAGE_SHADOW_LOG_DIR").map(std::path::PathBuf::from);
        if let Some(dir) = &shadow_log_dir {
            if let Err(e) = std::fs::create_dir_all(dir) {
                eprintln!(
                    "proof-coverage: warning: cannot create shadow log directory {}: {}",
                    dir.display(),
                    e
                );
            }
        }
        let shadow_events: Vec<_> = std::mem::take(&mut self.shadow_events)
            .into_iter()
            .filter_map(|(solver, events)| {
                let events: Vec<_> = events
                    .into_iter()
                    .filter(|event| match event {
                        shadow::ShadowEvent::Ambient { .. } => true,
                        shadow::ShadowEvent::Query { record_idx, .. } => {
                            self.queries[*record_idx].shadow_result.is_none()
                        }
                    })
                    .collect();
                events
                    .iter()
                    .any(|event| matches!(event, shadow::ShadowEvent::Query { .. }))
                    .then_some((solver, events))
            })
            .collect();
        let evidence_queries = shadow_events
            .iter()
            .map(|(_, events)| {
                events
                    .iter()
                    .filter(|event| matches!(event, shadow::ShadowEvent::Query { .. }))
                    .count()
            })
            .sum();
        let mut progress = EvidenceProgress::new(evidence_queries, shadow_events.len());
        for (solver, events) in shadow_events {
            if trace_shadow {
                eprintln!("proof-coverage-shadow: context={solver}");
                for event in &events {
                    if let shadow::ShadowEvent::Query { record_idx, .. } = event {
                        let q = &self.queries[*record_idx];
                        eprintln!(
                            "proof-coverage-shadow: plan record_idx={} q{} {} {} {:?}",
                            record_idx, q.id, q.family, q.fun, q.span
                        );
                    }
                }
            }
            let log_prefix =
                shadow_log_dir.as_ref().map(|dir| dir.join(format!("context-{solver}")));
            let context_queries = events
                .iter()
                .filter(|event| matches!(event, shadow::ShadowEvent::Query { .. }))
                .count();
            let completed_before = progress.completed;
            let outcomes = {
                let mut query_finished = |_| progress.query_finished();
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    shadow::solve_context(
                        &events,
                        trace_shadow,
                        minimize_cores,
                        log_prefix.as_deref(),
                        &mut query_finished,
                    )
                }))
            };
            match outcomes {
                Ok(outcomes) => {
                    for o in outcomes {
                        let q = &mut self.queries[o.record_idx];
                        q.shadow_result = Some(o.result.to_string());
                        q.core = o.core;
                        q.evidence_backend = o.evidence_backend.map(str::to_string);
                    }
                }
                Err(e) => {
                    let completed_in_context = progress.completed - completed_before;
                    progress.finish_failed_context(context_queries - completed_in_context);
                    let msg = e
                        .downcast_ref::<String>()
                        .map(|s| s.as_str())
                        .or_else(|| e.downcast_ref::<&str>().copied())
                        .unwrap_or("unknown panic");
                    eprintln!(
                        "proof-coverage: shadow solving failed for a context; queries left unmeasured ({})",
                        msg
                    );
                }
            }
        }
        let mut unavailable: BTreeMap<(String, String), u64> = BTreeMap::new();
        for q in &self.queries {
            let result = q.shadow_result.as_deref().unwrap_or("missing");
            if result != "valid" && !result.starts_with("canonical_") {
                *unavailable.entry((q.family.to_string(), result.to_string())).or_default() += 1;
            }
        }
        if !unavailable.is_empty() {
            let detail = unavailable
                .iter()
                .map(|((family, result), count)| format!("{} {}={}", family, result, count))
                .collect::<Vec<_>>()
                .join(", ");
            eprintln!(
                "proof-coverage: warning: shadow evidence unavailable ({detail}); \
                 affected terminals remain Unmeasured and emit no support edges"
            );
        }

        let (aligned, mismatched, alignment_derivations) = self.align_sst();
        if aligned > 0 || mismatched > 0 {
            eprintln!(
                "proof-coverage: sst alignment resolved {} occurrences ({} queries with count mismatch left unresolved)",
                aligned, mismatched
            );
        }
        let (artifacts, derivations) = self.build_structures(alignment_derivations);

        let mut summary = Summary::default();
        let mut buckets: BTreeMap<String, u64> = BTreeMap::new();
        summary.queries = self.queries.len() as u64;
        for q in &self.queries {
            for o in &q.occurrences {
                let unresolved = o.origin.kind == record::OriginKind::Unresolved;
                match o.role {
                    Role::Premise => {
                        summary.premises += 1;
                        if unresolved {
                            summary.unresolved_premises += 1;
                        }
                    }
                    Role::Obligation => {
                        summary.obligations += 1;
                        if unresolved {
                            summary.unresolved_obligations += 1;
                        }
                    }
                }
                if unresolved {
                    *buckets.entry(o.origin.detail.clone()).or_insert(0) += 1;
                }
            }
        }
        summary.unresolved_buckets = buckets.into_iter().collect();
        summary.results = self.results.iter().map(|(k, v)| (k.clone(), *v)).collect();

        eprintln!(
            "proof-coverage: {} queries, {} premises ({} unresolved), {} obligations ({} unresolved)",
            summary.queries,
            summary.premises,
            summary.unresolved_premises,
            summary.obligations,
            summary.unresolved_obligations
        );
        // Console-only evidence view (the record stays raw: labels + cores).
        let mut measured = 0u64;
        let mut used_premises = 0u64;
        let mut labeled_premises = 0u64;
        let mut checked_obligations = 0u64;
        let mut vacuous_obligations = 0u64;
        for q in &self.queries {
            let Some(core) = &q.core else { continue };
            measured += 1;
            let core: std::collections::BTreeSet<&String> = core.iter().collect();
            for o in &q.occurrences {
                let Some(label) = &o.label else { continue };
                match o.role {
                    Role::Premise => {
                        labeled_premises += 1;
                        if core.contains(label) {
                            used_premises += 1;
                        }
                    }
                    Role::Obligation => {
                        checked_obligations += 1;
                        if !core.contains(label) {
                            vacuous_obligations += 1;
                        }
                    }
                }
            }
        }
        eprintln!(
            "proof-coverage: {} measured queries; {}/{} premises used; {} obligations, {} vacuous",
            measured, used_premises, labeled_premises, checked_obligations, vacuous_obligations
        );
        // Core label resolution: every core label should be a query label
        // (statement/local occurrence), an ambient row, or is unknown.
        let mut core_query_labels = 0u64;
        let mut core_ambient_labels = 0u64;
        let mut core_unknown_labels = 0u64;
        let mut ambient_used: BTreeMap<&str, u64> = BTreeMap::new();
        {
            let mut query_labels: std::collections::BTreeSet<&String> =
                std::collections::BTreeSet::new();
            for q in &self.queries {
                for o in &q.occurrences {
                    if let Some(l) = &o.label {
                        query_labels.insert(l);
                    }
                }
                if let Some(t) = &q.target_label {
                    query_labels.insert(t);
                }
            }
            for q in &self.queries {
                let Some(core) = &q.core else { continue };
                for l in core {
                    if query_labels.contains(l) {
                        core_query_labels += 1;
                    } else if let Some(a) = self.ambients.get(l) {
                        core_ambient_labels += 1;
                        *ambient_used.entry(&a.owner).or_insert(0) += 1;
                    } else {
                        core_unknown_labels += 1;
                    }
                }
            }
        }
        eprintln!(
            "proof-coverage: core labels resolve to {} query occurrences, {} ambient axioms ({} owners), {} unknown",
            core_query_labels,
            core_ambient_labels,
            ambient_used.len(),
            core_unknown_labels
        );

        let mut focused_total = 0u64;
        let mut focused_measured = 0u64;
        let mut focused_vacuous = 0u64;
        let mut focused_support: u64 = 0;
        for q in &self.queries {
            if q.family != record::QueryFamily::Focused {
                continue;
            }
            focused_total += 1;
            let (Some(core), Some(target)) = (&q.core, &q.target_label) else { continue };
            focused_measured += 1;
            if core.iter().any(|l| l == target) {
                focused_support += (core.len() as u64).saturating_sub(1);
            } else {
                focused_vacuous += 1;
            }
        }
        if focused_total > 0 {
            let avg = if focused_measured > focused_vacuous {
                focused_support / (focused_measured - focused_vacuous)
            } else {
                0
            };
            eprintln!(
                "proof-coverage: {} focused queries ({} measured, {} vacuous terminals), avg support {} labels",
                focused_total, focused_measured, focused_vacuous, avg
            );
        }

        let record = CoverageRecord {
            schema: record::SCHEMA.to_string(),
            artifact_version: record::ARTIFACT_VERSION.to_string(),
            functions: std::mem::take(&mut self.functions),
            source_functions: self
                .source_functions
                .iter()
                .filter(|function| function.authored)
                .map(|function| function.source.clone())
                .collect(),
            queries: std::mem::take(&mut self.queries),
            ambients: std::mem::take(&mut self.ambients).into_values().collect(),
            checked_exports: std::mem::take(&mut self.checked_exports),
            refinements: self
                .source_functions
                .iter()
                .filter(|function| function.authored)
                .filter_map(|function| {
                    function
                        .refines
                        .as_ref()
                        .map(|trait_method| (function.fun.clone(), trait_method.clone()))
                })
                .collect(),
            artifacts,
            derivations,
            summary,
            // Filled in below, once the digest over this body is known.
            record_id: String::new(),
        };
        let out = std::env::var(OUT_ENV).unwrap_or_else(|_| OUT_DEFAULT.to_string());
        // Canonicalize identifiers into fingerprint order (byte-determinism
        // under parallel verification). The runtime guard refuses if two
        // contexts share a fingerprint but differ in ID-erased content; the
        // record is then emitted in arrival order with a warning.
        let mut value = match serde_json::to_value(&record) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("proof-coverage: failed to serialize record: {}", e);
                return;
            }
        };
        match proof_coverage_core::audit::canonicalize(&mut value) {
            Ok(()) => {}
            Err(e) => {
                eprintln!(
                    "proof-coverage: canonicalization refused ({}); emitting arrival order",
                    e
                );
            }
        }
        match proof_coverage_core::audit::compute_record_id(&value) {
            Ok(record_id) => {
                value
                    .as_object_mut()
                    .expect("CoverageRecord serializes as a JSON object")
                    .insert("record_id".to_string(), serde_json::Value::String(record_id));
            }
            Err(e) => {
                eprintln!("proof-coverage: record identity failed: {}", e);
                return;
            }
        }
        match serde_json::to_string_pretty(&value) {
            Ok(json) => {
                if let Err(e) = std::fs::write(&out, json) {
                    eprintln!("proof-coverage: failed to write {}: {}", out, e);
                } else {
                    eprintln!("proof-coverage: record written to {}", out);
                }
            }
            Err(e) => eprintln!("proof-coverage: serialization failed: {}", e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use air::ast::{Constant, ExprX};

    fn solver_config() -> SolverReplayConfig {
        SolverReplayConfig {
            solver: air::context::SmtSolver::Z3,
            option_history: vec![("air_recommended_options".to_string(), "true".to_string())],
            rlimit: 30_000_000,
            single_check_query: false,
            ignore_unexpected_smt: false,
            debug: false,
            expected_solver_version: None,
        }
    }

    fn unnamed_axiom() -> Commands {
        Arc::new(vec![Arc::new(CommandX::Global(Arc::new(DeclX::Axiom(Axiom {
            named: None,
            expr: Arc::new(ExprX::Const(Constant::Bool(true))),
        }))))])
    }

    fn installed_axiom_name(event: &shadow::ShadowEvent) -> Option<String> {
        let shadow::ShadowEvent::Ambient { commands, .. } = event else {
            panic!("expected ambient event");
        };
        let CommandX::Global(decl) = &*commands[0] else {
            panic!("expected global command");
        };
        let DeclX::Axiom(Axiom { named, .. }) = &**decl else {
            panic!("expected axiom");
        };
        named.as_ref().map(|name| name.to_string())
    }

    #[test]
    fn function_ambient_is_named_only_in_shadow_clone() {
        let commands = unnamed_axiom();
        let reason = ContextInstallReason::FunctionContext {
            op: "Broadcast".to_string(),
            owner: "crate::lemma".to_string(),
        };
        let mut producer = CoverageProducer::new();
        producer.handle_context_installed(7, &solver_config(), &reason, &commands);
        producer.handle_context_installed(9, &solver_config(), &reason, &commands);

        let original_name = match &*commands[0] {
            CommandX::Global(decl) => match &**decl {
                DeclX::Axiom(Axiom { named, .. }) => named,
                _ => panic!("expected axiom"),
            },
            _ => panic!("expected global command"),
        };
        assert!(original_name.is_none(), "canonical command was mutated");

        assert_eq!(producer.ambients.len(), 1);
        let ambient = producer.ambients.values().next().unwrap();
        assert_eq!(ambient.op, "Broadcast");
        assert_eq!(ambient.owner, "crate::lemma");
        assert_eq!(ambient.solver_contexts, vec![7, 9]);

        let first = installed_axiom_name(&producer.shadow_events[&7][0]).unwrap();
        let second = installed_axiom_name(&producer.shadow_events[&9][0]).unwrap();
        assert_eq!(first, ambient.label);
        assert_eq!(second, ambient.label);
        assert!(first.starts_with("pc_a%"));
    }

    #[test]
    fn setup_ambient_remains_background() {
        let commands = unnamed_axiom();
        let mut producer = CoverageProducer::new();
        producer.handle_context_installed(
            7,
            &solver_config(),
            &ContextInstallReason::Setup("Fuel".to_string()),
            &commands,
        );

        assert!(producer.ambients.is_empty());
        assert_eq!(producer.background_axioms.get(&7), Some(&1));
        assert!(installed_axiom_name(&producer.shadow_events[&7][0]).is_none());
    }

    #[test]
    fn canonical_failures_are_not_shadow_candidates() {
        assert_eq!(CoverageProducer::canonical_shadow_skip_reason(&[]), Some("canonical_missing"));
        assert_eq!(CoverageProducer::canonical_shadow_skip_reason(&["valid".to_string()]), None);
        assert_eq!(
            CoverageProducer::canonical_shadow_skip_reason(&[
                "invalid".to_string(),
                "valid".to_string(),
            ]),
            Some("canonical_invalid")
        );
        assert_eq!(
            CoverageProducer::canonical_shadow_skip_reason(&["canceled".to_string()]),
            Some("canonical_canceled")
        );
    }

    #[test]
    fn source_contract_inventory_does_not_depend_on_observed_queries() {
        let mut producer = CoverageProducer::new();
        producer.source_functions.push(SourceFunctionInventory {
            fun: "crate::declared_only".to_string(),
            authored: true,
            req_spans: vec!["inventory.rs:3:9".to_string()],
            ens_spans: vec!["inventory.rs:5:9".to_string()],
            dec_spans: Vec::new(),
            param_spans: Vec::new(),
            source: record::SourceFunction {
                fun: "crate::declared_only".to_string(),
                friendly: "crate::declared_only".to_string(),
                krate: "crate".to_string(),
                local: true,
                mode: record::FunctionMode::Exec,
                kind: record::FunctionKind::Static,
                item: record::ItemKind::Function,
                module: None,
                visibility: record::Visibility::Public,
                body_visibility: record::BodyVisibility::Visible {
                    visibility: record::Visibility::Public,
                },
                opaqueness: record::Opaqueness::Opaque,
                has_body: true,
                external_body: false,
                broadcast: false,
                span: None,
            },
            refines: None,
            body_artifacts: Vec::new(),
        });
        let mut generated_source = producer.source_functions[0].source.clone();
        generated_source.fun = "crate::generated_helper".to_string();
        generated_source.friendly = "crate::generated_helper".to_string();
        producer.source_functions.push(SourceFunctionInventory {
            fun: generated_source.fun.clone(),
            authored: false,
            req_spans: vec!["inventory.rs:20:9".to_string()],
            ens_spans: vec!["inventory.rs:21:9".to_string()],
            dec_spans: Vec::new(),
            param_spans: Vec::new(),
            source: generated_source,
            refines: None,
            body_artifacts: vec![SourceBodyArtifact {
                id: "crate::generated_helper#assign.src0".to_string(),
                kind: record::ArtifactKind::Assignment,
                span: "inventory.rs:22:5".to_string(),
                source_ids: Vec::new(),
                parent: Some("crate::generated_helper".to_string()),
                callee: None,
                group: None,
            }],
        });

        let (artifacts, derivations) = producer.build_structures(Vec::new());
        let ids = artifacts.iter().map(|artifact| artifact.id.as_str()).collect::<BTreeSet<_>>();

        assert!(ids.contains("crate::declared_only"));
        assert!(ids.contains("crate::declared_only#req"));
        assert!(ids.contains("crate::declared_only#req[0]"));
        assert!(ids.contains("crate::declared_only#ens"));
        assert!(ids.contains("crate::declared_only#ens[0]"));
        assert!(!ids.iter().any(|id| id.starts_with("crate::generated_helper")));
        assert!(derivations.is_empty());
    }

    #[test]
    fn span_join_requires_unique_artifact_identity() {
        let key = ("crate::f".to_string(), "same.rs:3:9".to_string());
        let unique = BTreeMap::from([(key.clone(), vec!["crate::f#req[0]".to_string()])]);
        assert_eq!(unique_join(&unique, &key).as_deref(), Some("crate::f#req[0]"));

        let ambiguous = BTreeMap::from([(
            key.clone(),
            vec!["crate::f#req[0]".to_string(), "crate::f#req[1]".to_string()],
        )]);
        assert_eq!(unique_join(&ambiguous, &key), None);
    }

    /// The declaration-level sidecar attributes query-local axioms by the
    /// construction that emitted them. A requires clause is attributed by
    /// its declaring ordinal (not by count agreement), a parameter type
    /// invariant gets the parameter's span as its site, and a Decl the
    /// sidecar does not cover keeps the vocabulary classification only.
    #[test]
    fn local_axiom_sidecar_attributes_by_construction_site() {
        use vir::observer::{EmissionSlotMap, LocalAxiomMap, LocalAxiomSite};

        let opaque = |name: &str| -> air::ast::Decl {
            Arc::new(DeclX::Axiom(Axiom {
                named: None,
                expr: Arc::new(ExprX::Var(Arc::new(name.to_string()))),
            }))
        };
        // Two requires clauses with an unrelated axiom between them: the
        // ordinal comes from the sidecar, never from the position in `local`.
        let req1 = opaque("r1");
        let stray = opaque("stray");
        let req0 = opaque("r0");
        let param0 = opaque("p0");
        let local: air::ast::Decls =
            Arc::new(vec![req1.clone(), stray, req0.clone(), param0.clone()]);

        let mut local_axioms = LocalAxiomMap::new();
        local_axioms.insert(Arc::as_ptr(&req1) as usize, LocalAxiomSite::Requires { clause: 1 });
        local_axioms.insert(Arc::as_ptr(&req0) as usize, LocalAxiomSite::Requires { clause: 0 });
        local_axioms
            .insert(Arc::as_ptr(&param0) as usize, LocalAxiomSite::ParamTypeInvariant { param: 0 });

        let statements = LoweringProvenanceMap::new();
        let slots = EmissionSlotMap::new();
        let mut walk = QueryWalk {
            occurrences: Vec::new(),
            sites: Vec::new(),
            path: Vec::new(),
            lowering_provenance: &statements,
            sst_sites: None,
            require_lowering_provenance: false,
            missing_lowering_sites: Vec::new(),
            join_stmts: BTreeMap::new(),
            last_assert: None,
            assert_pairs: Vec::new(),
            pending_forall: Vec::new(),
            forall_pairs: Vec::new(),
            armed_exit_invs: Vec::new(),
            recent_establish: Vec::new(),
            armed_exit_cond: false,
            emission_slots: &slots,
            loop_clause_spans: BTreeMap::new(),
            local_axioms: &local_axioms,
            req_spans: vec!["f.rs:2:9".to_string(), "f.rs:3:9".to_string()],
            ens_spans: Vec::new(),
            param_spans: vec!["f.rs:1:6".to_string()],
            loop_spans_by_id: BTreeMap::new(),
            lemma_clauses: BTreeMap::new(),
            query_span: "f.rs:1:1".to_string(),
        };
        walk.walk_local_axioms(&local);

        let o = &walk.occurrences;
        assert_eq!(o.len(), 4);
        assert_eq!(
            walk.sites,
            (0..4).map(QuerySiteId::LocalAxiom).collect::<Vec<_>>(),
            "site ordinals follow position in `local`"
        );

        assert_eq!(o[0].origin.kind, record::OriginKind::Source);
        assert_eq!(o[0].origin.detail, "requires[1]");
        assert_eq!(o[0].span.as_deref(), Some("f.rs:3:9"));
        assert_eq!(o[0].phase().as_deref(), Some("function.requires"));
        assert_eq!(o[0].emission, Some(EmissionRole::FunctionRequires { clause: 1 }));
        assert_eq!(o[0].rule.as_deref(), Some(rules::R_EMITTED_AXIOM));

        assert_eq!(o[1].origin.kind, record::OriginKind::Unresolved, "uncovered Decl stays a gap");
        assert!(o[1].shape.is_some());
        assert!(o[1].span.is_none());

        assert_eq!(o[2].origin.detail, "requires[0]");
        assert_eq!(o[2].span.as_deref(), Some("f.rs:2:9"));

        assert_eq!(o[3].origin.kind, record::OriginKind::Generated);
        assert_eq!(o[3].origin.detail, "type_invariant");
        assert_eq!(o[3].phase().as_deref(), Some("function.param_type_invariant"));
        assert_eq!(o[3].span.as_deref(), Some("f.rs:1:6"));
        assert!(o[3].node.is_none(), "a Decl has no CFG placement");
    }
}
