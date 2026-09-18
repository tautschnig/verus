//! L2: the fact graph.
//!
//! A mechanical, policy-free translation of one or more records into graph
//! vocabulary. Everything here is a re-statement of something the record
//! observed; nothing here is a claim about what proof dependency means. The
//! test (`PROOF_COVERAGE_DESIGN.md` §3): if a reviewer rejected the
//! analyzer's definition of dependency, no row produced by this module would
//! change.
//!
//! The only evidence-bearing relation, `SupportedBy`, enters through exactly
//! one function, [`evidence`], which is the sole reader of a query's `core`
//! and `shadow_result`. A second measurement backend (for example
//! delete-and-reverify) would be admitted there and nowhere else.
//!
//! Three more relations are materialized here because they are structural,
//! not inferential: `TerminalOf` (the recorded terminal split), `Aggregates`
//! (the recorded artifact tree), and the weak joint `ObservedInBatch`
//! display arcs.
//! Licensing rules — loops, lemmas, asserts, contracts, induction — live in
//! [`crate::licensing`] and consume the tables built here.

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::{Arc, ArcKind, VertexInfo};
use crate::record::{
    ArtifactKind, CoverageRecord, EmissionRole, LoopInvariantGroup, Occurrence, OriginKind,
    QueryFamily, QueryRecord, Role,
};

/// Premises and ambient facts available while checking an obligation.
///
/// Scope is metadata, separate from evidence: a batch core is one joint
/// premise-set → obligation-set observation and does not encode a separate
/// dependency for each obligation. Terminal obligations inherit the scope of
/// their batch parent.
#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct ObligationScope {
    pub solver_context: u64,
    pub terminal_path: Option<String>,
    pub available: BTreeSet<String>,
    pub ambients: BTreeSet<String>,
}

/// Exact call-site identity for a call-postcondition premise.
#[derive(Clone)]
pub struct CallBoundaryInfo {
    pub caller: String,
    pub callee: Option<String>,
    pub cfg_node: Option<String>,
    pub call_artifact: Option<String>,
    /// The call targets a member of the caller's call-graph SCC.
    pub recursive: bool,
    /// The call is preceded by the recursion encoding's decrease guard.
    pub guarded_recursive: bool,
}

/// One labelled batch occurrence, with its identities already namespaced for
/// the combined graph.
pub struct FactRow<'r> {
    /// Namespaced vertex identity.
    pub label: String,
    pub occurrence: &'r Occurrence,
    pub query: &'r QueryRecord,
    /// Namespaced artifact identity, when the occurrence projects onto one.
    pub artifact: Option<String>,
}

/// The facts of one record, namespaced when several records are combined.
pub struct RecordFacts<'r> {
    pub record: &'r CoverageRecord,
    pub index: usize,
    multi: bool,
    /// artifact id → the record whose crate defines the artifact's owner.
    /// A callee's contract aggregate imported into this record is the same
    /// artifact as the callee's own aggregate in the record that verified it;
    /// namespacing both under the defining record is what lets a modular
    /// slice cross the crate boundary. Owners defined locally by no record, or
    /// by more than one (two versions of a crate), stay record-local.
    artifact_home: BTreeMap<String, usize>,
    /// Labelled batch occurrences, in label order.
    pub rows: Vec<FactRow<'r>>,
    /// artifact → (label, role) of every occurrence projecting onto it, in
    /// label order. Licensing rules quantify over this.
    pub by_artifact: BTreeMap<String, Vec<(String, EmissionRole)>>,
    /// (caller, cfg node) → the call at that node.
    pub call_sites: BTreeMap<(String, String), CallBoundaryInfo>,
}

impl<'r> RecordFacts<'r> {
    /// Namespace a label or β vertex for the combined graph.
    pub fn ns(&self, l: &str) -> String {
        if self.multi { format!("r{}%{}", self.index, l) } else { l.to_string() }
    }

    /// Namespace an artifact identity under the record that defines its
    /// owner. Friendly function-qualified names are not globally unique
    /// across crates, versions, or independent runs, so an artifact whose
    /// owner no record defines locally — or two records do — keeps this
    /// record's namespace.
    pub fn ns_artifact(&self, a: &str) -> String {
        if !self.multi {
            return a.to_string();
        }
        let home = self.artifact_home.get(a).copied().unwrap_or(self.index);
        format!("r{}%{}", home, a)
    }

    /// Rows of one artifact at one protocol position.
    pub fn at(&self, artifact: &str, role: &EmissionRole) -> Vec<String> {
        self.by_artifact
            .get(artifact)
            .map(|rows| rows.iter().filter(|(_, r)| r == role).map(|(l, _)| l.clone()).collect())
            .unwrap_or_default()
    }

    /// Batch queries whose canonical run succeeded (shadow measurement may
    /// still be absent); the queries whose occurrences describe the proof.
    pub fn interpreted_batches(&self) -> impl Iterator<Item = &'r QueryRecord> + '_ {
        self.record.queries.iter().filter(|q| {
            q.family == QueryFamily::Batch
                && !q.shadow_result.as_deref().is_some_and(|r| r.starts_with("canonical_"))
        })
    }
}

/// The fact graph over all input records.
pub struct Facts<'r> {
    pub records: Vec<RecordFacts<'r>>,
    /// Evidence and structural arcs: `SupportedBy`, `ObservedInBatch`,
    /// `TerminalOf`, `Aggregates`.
    pub arcs: Vec<Arc>,
    pub vertex_info: BTreeMap<String, VertexInfo>,
    pub obligations: BTreeSet<String>,
    pub premises: BTreeSet<String>,
    pub spec_obligations: BTreeSet<String>,
    pub covered: BTreeSet<String>,
    pub vacuous: BTreeSet<String>,
    pub ambient_roots: BTreeSet<String>,
    pub background_roots: BTreeSet<String>,
    pub elaborates: BTreeMap<String, BTreeSet<String>>,
    pub artifact_children: BTreeMap<String, BTreeSet<String>>,
    /// artifact → declared clause group (loop invariants). The loop rule
    /// derives its licensing tails from this.
    pub artifact_group: BTreeMap<String, LoopInvariantGroup>,
    pub artifact_ids: BTreeSet<String>,
    pub unresolved_premises_of: BTreeMap<String, u64>,
    pub ambient_owner: BTreeMap<String, String>,
    pub ambient_op: BTreeMap<String, String>,
    pub obligation_scopes: BTreeMap<String, ObligationScope>,
    pub call_boundaries: BTreeMap<String, CallBoundaryInfo>,
    /// Obligations that received a completed measurement or a terminal
    /// conjunction; the complement is `unmeasured`.
    pub supported_heads: BTreeSet<String>,
    /// (record index, record-local artifact id) → graph vertex. Consumers
    /// that hold a record-local artifact reference (findings, projections)
    /// resolve it here rather than re-deriving the namespacing.
    pub artifact_vertex: BTreeMap<(usize, String), String>,
    /// artifact vertex → owning trait method, for contract clauses declared
    /// on a trait (`SourceFunction.kind == TraitMethodDecl`).
    pub trait_declared: BTreeMap<String, String>,
    /// occurrence vertex → owning function.
    pub function_of: BTreeMap<String, String>,
}

/// What one query's measurement says, as a relation over vertices.
///
/// This is the single door through which solver evidence enters the graph.
/// It is the only code that reads `QueryRecord.core`.
pub enum Evidence {
    /// The query was not measured.
    NotMeasured,
    /// A batch core: a joint witness for the whole batch, which cannot say
    /// which obligation consumed which premise. Display only.
    Batch { members: BTreeSet<String> },
    /// A focused core whose terminal was observed: the members jointly
    /// support the terminal.
    Support { terminal: String, members: BTreeSet<String> },
    /// A focused core whose terminal was absent: a contradiction witness.
    /// It explains the discharge but supports nothing.
    Contradiction { terminal: String, members: BTreeSet<String> },
}

/// The evidence one query contributes, in record-local (un-namespaced) labels.
pub fn evidence(q: &QueryRecord) -> Evidence {
    let Some(core) = &q.core else { return Evidence::NotMeasured };
    let members: BTreeSet<String> = core.iter().cloned().collect();
    match q.family {
        QueryFamily::Batch => Evidence::Batch { members },
        QueryFamily::Focused => {
            let Some(target) = &q.target_label else { return Evidence::NotMeasured };
            let mut members = members;
            if members.remove(target) {
                Evidence::Support { terminal: target.clone(), members }
            } else {
                Evidence::Contradiction { terminal: target.clone(), members }
            }
        }
    }
}

/// The callee whose contract a call consumed: the statically resolved
/// implementation when the verifier resolved trait dispatch, else the
/// syntactic target. `callee` is the call site's recorded syntactic callee.
pub fn consumed_callee<'r>(
    func: &'r crate::record::FunctionRecord,
    node: &str,
    callee: &'r Option<String>,
) -> Option<&'r str> {
    func.resolved_calls
        .iter()
        .find(|(n, _)| n == node)
        .map(|(_, r)| r.as_str())
        .or(callee.as_deref())
}

/// Build the fact graph.
pub fn facts(records: &[CoverageRecord]) -> Facts<'_> {
    let mut f = Facts {
        records: Vec::new(),
        arcs: Vec::new(),
        vertex_info: BTreeMap::new(),
        obligations: BTreeSet::new(),
        premises: BTreeSet::new(),
        spec_obligations: BTreeSet::new(),
        covered: BTreeSet::new(),
        vacuous: BTreeSet::new(),
        ambient_roots: BTreeSet::new(),
        background_roots: BTreeSet::new(),
        elaborates: BTreeMap::new(),
        artifact_children: BTreeMap::new(),
        artifact_group: BTreeMap::new(),
        artifact_ids: BTreeSet::new(),
        unresolved_premises_of: BTreeMap::new(),
        ambient_owner: BTreeMap::new(),
        ambient_op: BTreeMap::new(),
        obligation_scopes: BTreeMap::new(),
        call_boundaries: BTreeMap::new(),
        supported_heads: BTreeSet::new(),
        artifact_vertex: BTreeMap::new(),
        trait_declared: BTreeMap::new(),
        function_of: BTreeMap::new(),
    };
    let multi = records.len() > 1;
    let definers = definers(records);
    for (ri, record) in records.iter().enumerate() {
        let rf = record_facts(record, ri, multi, &definers, &mut f);
        f.records.push(rf);
    }
    f
}

/// function → the one record whose crate defines it locally. Functions no
/// record defines (imported everywhere) or that two records define (two
/// versions of a crate in one project) are absent, and stay record-local.
fn definers(records: &[CoverageRecord]) -> BTreeMap<String, usize> {
    let mut seen: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    for (ri, record) in records.iter().enumerate() {
        for sf in record.source_functions.iter().filter(|sf| sf.local) {
            seen.entry(sf.fun.as_str()).or_default().push(ri);
        }
    }
    seen.into_iter()
        .filter_map(|(fun, records)| match records.as_slice() {
            [one] => Some((fun.to_string(), *one)),
            _ => None,
        })
        .collect()
}

fn record_facts<'r>(
    record: &'r CoverageRecord,
    index: usize,
    multi: bool,
    definers: &BTreeMap<String, usize>,
    f: &mut Facts<'r>,
) -> RecordFacts<'r> {
    let artifact_home = record
        .artifacts
        .iter()
        .filter_map(|a| definers.get(&a.owner).map(|home| (a.id.clone(), *home)))
        .collect();
    let mut rf = RecordFacts {
        record,
        index,
        multi,
        artifact_home,
        rows: Vec::new(),
        by_artifact: BTreeMap::new(),
        call_sites: BTreeMap::new(),
    };

    // ── ambient axioms: owner and installing op, per solver context ────────
    let ambient_owner: BTreeMap<&str, &str> =
        record.ambients.iter().map(|a| (a.label.as_str(), a.owner.as_str())).collect();
    let ambient_op: BTreeMap<&str, &str> =
        record.ambients.iter().map(|a| (a.label.as_str(), a.op.as_str())).collect();
    let mut ambients_in_context: BTreeMap<u64, BTreeSet<String>> = BTreeMap::new();
    for a in &record.ambients {
        let label = rf.ns(&a.label);
        f.ambient_owner.insert(label.clone(), a.owner.clone());
        f.ambient_op.insert(label.clone(), a.op.clone());
        for context in &a.solver_contexts {
            ambients_in_context.entry(*context).or_default().insert(label.clone());
        }
    }

    // ── call sites: recorded calls, SCC membership, decrease guards ────────
    // Recursion is a property of the recorded call-site graph: a call is
    // recursive when its callee reaches the caller. Which recursive calls
    // are guarded is a separate recorded fact (the decrease-guard block the
    // recursion encoding inserts).
    let function_names: BTreeSet<&str> = record.functions.iter().map(|f| f.fun.as_str()).collect();
    let mut call_adj: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for func in &record.functions {
        for (node, _, callee) in &func.call_sites {
            if let Some(callee) = consumed_callee(func, node, callee) {
                if function_names.contains(callee) {
                    call_adj.entry(func.fun.as_str()).or_default().push(callee);
                }
            }
        }
    }
    let reaches = |start: &str, target: &str| -> bool {
        let mut seen = BTreeSet::new();
        let mut stack = vec![start];
        while let Some(fun) = stack.pop() {
            if fun == target {
                return true;
            }
            if !seen.insert(fun) {
                continue;
            }
            if let Some(next) = call_adj.get(fun) {
                stack.extend(next.iter().copied());
            }
        }
        false
    };
    let guarded_recursive_nodes: BTreeSet<(String, String)> = record
        .functions
        .iter()
        .flat_map(|function| {
            function
                .recursive_calls
                .iter()
                .map(|call| (function.fun.clone(), call.call_node.clone()))
        })
        .collect();
    let mut recursive_nodes: BTreeSet<(String, String)> = BTreeSet::new();
    for func in &record.functions {
        for (node, _, callee) in &func.call_sites {
            if consumed_callee(func, node, callee).is_some_and(|callee| reaches(callee, &func.fun))
            {
                recursive_nodes.insert((func.fun.clone(), node.clone()));
            }
        }
    }
    for func in &record.functions {
        for (node, _, callee) in &func.call_sites {
            let key = (func.fun.clone(), node.clone());
            rf.call_sites.insert(
                key.clone(),
                CallBoundaryInfo {
                    caller: func.fun.clone(),
                    callee: consumed_callee(func, node, callee).map(str::to_string),
                    cfg_node: Some(node.clone()),
                    call_artifact: None,
                    recursive: recursive_nodes.contains(&key),
                    guarded_recursive: guarded_recursive_nodes.contains(&key),
                },
            );
        }
    }
    // Prefer the emitted call-site artifact over reconstructing its id.
    // Older records without artifacts still retain caller/callee/node from
    // Function.call_sites and simply report no artifact at the boundary.
    for artifact in record.artifacts.iter().filter(|a| a.kind == ArtifactKind::CallSite) {
        let Some(node) = &artifact.cfg_node else { continue };
        let key = (artifact.owner.clone(), node.clone());
        let recursive = recursive_nodes.contains(&key);
        let guarded_recursive = guarded_recursive_nodes.contains(&key);
        let call_artifact = Some(rf.ns_artifact(&artifact.id));
        rf.call_sites
            .entry(key)
            .and_modify(|call| {
                call.callee = artifact.callee.clone().or_else(|| call.callee.clone());
                call.call_artifact = call_artifact.clone();
            })
            .or_insert_with(|| CallBoundaryInfo {
                caller: artifact.owner.clone(),
                callee: artifact.callee.clone(),
                cfg_node: Some(node.clone()),
                call_artifact,
                recursive,
                guarded_recursive,
            });
    }

    // ── occurrences: one vertex per label ──────────────────────────────────
    // Labels are unique per record (the query id is embedded), so a label
    // keyed map is a total index. Rows are kept in label order.
    let mut occ_of: BTreeMap<&str, (&Occurrence, &QueryRecord)> = BTreeMap::new();
    for q in &record.queries {
        for o in &q.occurrences {
            if let Some(l) = &o.label {
                occ_of.insert(l.as_str(), (o, q));
            }
        }
    }
    for q in &record.queries {
        if q.family == QueryFamily::Batch {
            let n = q
                .occurrences
                .iter()
                .filter(|o| o.role == Role::Premise && o.origin.kind == OriginKind::Unresolved)
                .count() as u64;
            if n > 0 {
                *f.unresolved_premises_of.entry(q.fun.clone()).or_default() += n;
            }
        }
    }
    for (label, (o, q)) in &occ_of {
        let vertex = rf.ns(label);
        let artifact = o.artifact.as_deref().map(|a| rf.ns_artifact(a));
        let info = f.vertex_info.entry(vertex.clone()).or_default();
        info.detail = o.origin.detail.clone();
        info.origin_kind = Some(o.origin.kind);
        info.role = Some(o.role);
        info.carrier = Some(o.carrier);
        info.span = o.span.clone();
        info.fun = Some(q.fun.clone());
        info.node = o.node.clone();
        info.artifact = artifact.clone();
        info.emission = o.emission.clone();
        info.phase = o.phase();
        info.unresolved = o.origin.kind == OriginKind::Unresolved;
        info.rule = o.rule.clone();
        info.join_rule = o.join_rule.clone();
        f.function_of.insert(vertex.clone(), q.fun.clone());
        match o.role {
            Role::Obligation => {
                f.obligations.insert(vertex.clone());
                if o.emission == Some(EmissionRole::FunctionEnsures) {
                    f.spec_obligations.insert(vertex.clone());
                }
            }
            Role::Premise => {
                f.premises.insert(vertex.clone());
                if matches!(o.emission, Some(EmissionRole::CallPostcondition { .. })) {
                    if let Some(node) = &o.node {
                        if let Some(call) = rf.call_sites.get(&(q.fun.clone(), node.clone())) {
                            f.call_boundaries.insert(vertex.clone(), call.clone());
                        }
                    }
                }
            }
        }
        // ElaboratesTo (deletion/display relation, not a derivation arc)
        if let Some(a) = &artifact {
            f.elaborates.entry(a.clone()).or_default().insert(vertex.clone());
            if let Some(role) = &o.emission {
                rf.by_artifact.entry(a.clone()).or_default().push((vertex.clone(), role.clone()));
            }
        }
        rf.rows.push(FactRow { label: vertex, occurrence: o, query: q, artifact });
    }

    // ── artifacts: vertices, tree, declared groups ─────────────────────────
    let trait_decls: BTreeSet<&str> = record
        .source_functions
        .iter()
        .filter(|sf| matches!(sf.kind, crate::record::FunctionKind::TraitMethodDecl { .. }))
        .map(|sf| sf.fun.as_str())
        .collect();
    for a in &record.artifacts {
        let artifact_id = rf.ns_artifact(&a.id);
        f.artifact_vertex.insert((index, a.id.clone()), artifact_id.clone());
        f.artifact_ids.insert(artifact_id.clone());
        if a.kind.is_clause() && trait_decls.contains(a.owner.as_str()) {
            f.trait_declared.insert(artifact_id.clone(), a.owner.clone());
        }
        let info = f.vertex_info.entry(artifact_id.clone()).or_default();
        if info.detail.is_empty() {
            info.detail = a.kind.to_string();
            info.span = a.span.clone();
            info.fun = Some(a.owner.clone());
        }
        if let Some(group) = &a.group {
            f.artifact_group.insert(artifact_id.clone(), *group);
        }
        if let Some(p) = &a.parent {
            f.artifact_children.entry(rf.ns_artifact(p)).or_default().insert(artifact_id);
        }
    }

    // ── terminals and evidence ─────────────────────────────────────────────
    let mut terminals_of: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for q in &record.queries {
        // A focused query defines a terminal even when measuring it fails.
        // Register every terminal and every parent relation before
        // inspecting the core; otherwise a canceled terminal of a
        // conjunction is silently omitted and the measured siblings can
        // incorrectly make the parent look fully supported.
        if q.family == QueryFamily::Focused {
            if let Some(target) = &q.target_label {
                let target = rf.ns(target);
                let mut available: BTreeSet<String> =
                    q.available.iter().map(|label| rf.ns(label)).collect();
                available.remove(&target);
                let scope = ObligationScope {
                    solver_context: q.solver_context,
                    terminal_path: q.terminal_path.clone(),
                    available,
                    ambients: ambients_in_context
                        .get(&q.solver_context)
                        .cloned()
                        .unwrap_or_default(),
                };
                if let Some(parent) = &q.parent_obligation_label {
                    let parent = rf.ns(parent);
                    let mut parent_scope = scope.clone();
                    parent_scope.terminal_path = None;
                    let inherited = if let Some(existing) = f.obligation_scopes.get(&parent) {
                        existing.clone()
                    } else {
                        f.obligation_scopes.insert(parent, parent_scope.clone());
                        parent_scope
                    };
                    let mut terminal_scope = inherited;
                    terminal_scope.terminal_path = q.terminal_path.clone();
                    f.obligation_scopes.insert(target.clone(), terminal_scope);
                } else {
                    f.obligation_scopes.insert(target.clone(), scope);
                }
                f.obligations.insert(target.clone());
                let info = f.vertex_info.entry(target.clone()).or_default();
                info.detail = "terminal".to_string();
                info.fun = Some(q.fun.clone());
                f.function_of.insert(target.clone(), q.fun.clone());
                if let Some(parent) = &q.parent_obligation_label {
                    terminals_of.entry(rf.ns(parent)).or_default().insert(target);
                }
            }
        }

        let ev = evidence(q);
        let members = match &ev {
            Evidence::NotMeasured => continue,
            Evidence::Batch { members }
            | Evidence::Support { members, .. }
            | Evidence::Contradiction { members, .. } => members,
        };
        for l in members {
            f.covered.insert(rf.ns(l));
        }
        if let Evidence::Support { terminal, .. } = &ev {
            // The terminal was in the core: covered like any other member. A
            // contradiction witness's terminal was not, and stays uncovered.
            f.covered.insert(rf.ns(terminal));
        }
        let beta = rf.ns(&format!("β:{}", q.id));
        f.background_roots.insert(beta.clone());
        // An ambient axiom named in a core is an evidence vertex: a root with
        // its recorded owner and installing op.
        let mut note_ambient = |l: &str| {
            if let Some(owner) = ambient_owner.get(l) {
                f.ambient_roots.insert(rf.ns(l));
                f.ambient_owner.insert(rf.ns(l), owner.to_string());
                if let Some(op) = ambient_op.get(l) {
                    f.ambient_op.insert(rf.ns(l), op.to_string());
                }
            }
        };
        match ev {
            Evidence::NotMeasured => unreachable!(),
            Evidence::Batch { members } => {
                // One weak set-to-set observation for the whole core. The
                // batch says only that these premises and obligations
                // participated jointly; per-obligation scopes live in
                // `obligation_scopes`, not in fabricated prefix arcs.
                let mut tail: BTreeSet<String> = BTreeSet::from([beta.clone()]);
                let mut head: BTreeSet<String> = BTreeSet::new();
                for l in &members {
                    match occ_of.get(l.as_str()) {
                        Some((occurrence, _)) => match occurrence.role {
                            Role::Premise => {
                                tail.insert(rf.ns(l));
                            }
                            Role::Obligation => {
                                head.insert(rf.ns(l));
                            }
                        },
                        None => {
                            tail.insert(rf.ns(l));
                            note_ambient(l);
                        }
                    }
                }
                for o in &q.occurrences {
                    if o.role == Role::Obligation {
                        if let Some(l) = &o.label {
                            if !members.contains(l) {
                                f.vacuous.insert(rf.ns(l));
                            }
                        }
                    }
                }
                if !head.is_empty() {
                    f.arcs.push(Arc {
                        tail,
                        head,
                        kind: ArcKind::ObservedInBatch,
                        query: Some(q.id),
                        why: format!("joint batch witness, query {} (not proof dependence)", q.id),
                    });
                }
            }
            Evidence::Contradiction { terminal, .. } => {
                // A returned core is a completed measurement even when it
                // demonstrates vacuity by omitting the focused target. Keep
                // that case distinct from an unavailable measurement, but do
                // not manufacture proof support for it.
                let terminal = rf.ns(&terminal);
                f.supported_heads.insert(terminal.clone());
                f.vacuous.insert(terminal);
            }
            Evidence::Support { terminal, members } => {
                let terminal_vertex = rf.ns(&terminal);
                f.supported_heads.insert(terminal_vertex.clone());
                // Scope guard: only labels this query offered may enter a
                // tail (occurrence-derived scope; a regression cannot
                // silently fabricate dependencies).
                let scope: BTreeSet<&str> = q.available.iter().map(|s| s.as_str()).collect();
                let mut tail: BTreeSet<String> = BTreeSet::from([beta.clone()]);
                for l in &members {
                    if occ_of.contains_key(l.as_str()) {
                        if !scope.is_empty() && !scope.contains(l.as_str()) {
                            continue;
                        }
                    } else {
                        note_ambient(l);
                    }
                    tail.insert(rf.ns(l));
                }
                f.arcs.push(Arc {
                    tail,
                    head: BTreeSet::from([terminal_vertex]),
                    kind: ArcKind::SupportedBy,
                    query: Some(q.id),
                    why: format!("focused query {} unsat core", q.id),
                });
            }
        }
    }

    // TerminalOf: obligation = conjunction of its terminals.
    for (obligation, terminals) in terminals_of {
        f.supported_heads.insert(obligation.clone());
        f.arcs.push(Arc {
            tail: terminals,
            head: BTreeSet::from([obligation]),
            kind: ArcKind::TerminalOf,
            query: None,
            why: "conjunction of the obligation's terminals".into(),
        });
    }

    rf
}

/// Aggregates: {clause artifacts} → aggregate artifact, from the recorded
/// artifact tree. Structural, not a licensing rule; emitted after the
/// licensing rules so that arc order matches the prior single-pass builder.
pub fn aggregate_arcs(rf: &RecordFacts<'_>) -> Vec<Arc> {
    let mut children: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for a in &rf.record.artifacts {
        if a.kind.is_clause() {
            if let Some(p) = &a.parent {
                children.entry(rf.ns_artifact(p)).or_default().insert(rf.ns_artifact(&a.id));
            }
        }
    }
    children
        .into_iter()
        .map(|(agg, clauses)| Arc {
            tail: clauses,
            head: BTreeSet::from([agg]),
            kind: ArcKind::Aggregates,
            query: None,
            why: "conjunction of the aggregate's clauses".into(),
        })
        .collect()
}
