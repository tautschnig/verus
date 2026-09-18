//! `pc-analyze` — typed verification-argument graph queries.
//!
//! Usage:
//!   pc-analyze <record.json>... summary
//!   pc-analyze <record.json>... backward  <vertex>
//!   pc-analyze <record.json>... forward   <vertex>...
//!   pc-analyze <record.json>... counterfactual <vertex>
//!   pc-analyze <record.json>... vertices [filter]
//!   pc-analyze <record.json>... targets [filter]
//!   pc-analyze <record.json>... slice <target> [opaque|modular]
//!   pc-analyze <record.json>... study [function-or-target] [opaque|modular]
//!   pc-analyze <record.json>... impact <artifact-or-vertex> [opaque|modular]
//!   pc-analyze <record.json>... report [opaque|modular]
//!   pc-analyze <record.json>... project [opaque|modular]
//!
//! Vertices are occurrence labels (`pc%q%n`) and artifact ids
//! (`crate::f#inv0[2]`). Counterfactual on an artifact ablates the artifact:
//! all its occurrences (including its own generated obligations) are
//! deleted, and only surviving obligations are reported. Artifact
//! projection is display-only.

use proof_coverage::analysis::{self, Boundary, CallPolicy, Graph, Slice, SliceOptions, SliceStep};
use proof_coverage::projection::{self, QueryFinding, ScopeProjection};
use proof_coverage::record::{self, Carrier, CoverageRecord, OriginKind, QueryFamily};
use std::collections::{BTreeMap, BTreeSet};

fn call_policy(arg: Option<&String>) -> CallPolicy {
    match arg.map(String::as_str).unwrap_or("opaque") {
        "opaque" => CallPolicy::Opaque,
        "modular" => CallPolicy::Modular,
        other => {
            eprintln!("unknown call policy {other}; expected opaque or modular");
            std::process::exit(2);
        }
    }
}

fn slice_status(g: &Graph, slice: &Slice, fail_open: &BTreeSet<String>) -> &'static str {
    if slice
        .boundaries
        .iter()
        .any(|b| matches!(b, Boundary::Ungrounded { vertex } if vertex == &slice.target))
    {
        "Ungrounded"
    } else if !slice.possible.is_empty() {
        "Overapproximated"
    } else if slice.definite.iter().any(|v| {
        g.vertex_info.get(v).is_some_and(|i| {
            i.unresolved
                || (matches!(i.carrier, Some(Carrier::Assume | Carrier::Assert))
                    && i.node.is_none())
                || (i.origin_kind == Some(OriginKind::Source) && i.artifact.is_none())
        })
        // An unlicensed exported assumption in the slice is an incomplete
        // measurement of the argument, so it cannot report `Complete`. Without
        // this, a slice whose supporting facts silently dropped out looks
        // fully measured and its absence findings look defensible.
        || fail_open.contains(v)
    }) {
        "Partial"
    } else {
        "Complete"
    }
}

/// Graph roots that are really an assumption some checked construct exported,
/// i.e. holes in the licensing relation. `PROOF_COVERAGE_FINDINGS.md` §5 lists
/// "exported assumptions lacking a licensing relation" as a required
/// diagnostic: such a root is taken on trust, so every fact that supported
/// only its discharge drops out of the slice and is reported unused. Findings
/// in a slice containing one of these cannot be defended.
fn fail_open_roots(g: &Graph) -> BTreeSet<String> {
    g.roots()
        .into_iter()
        .filter(|vertex| {
            g.vertex_info.get(vertex).and_then(|info| info.emission.as_ref()).is_some_and(
                |emission| {
                    matches!(
                        root_expectation(emission).0,
                        RootBucket::NoRule | RootBucket::RuleDidNotFire
                    )
                },
            )
        })
        .collect()
}

fn completeness_json(g: &Graph, slice: &Slice, fail_open: &BTreeSet<String>) -> serde_json::Value {
    let infos: Vec<_> =
        slice.definite.iter().filter_map(|vertex| g.vertex_info.get(vertex)).collect();
    let unresolved = infos.iter().filter(|info| info.unresolved).count();
    let statements: Vec<_> = infos
        .iter()
        .filter(|info| matches!(info.carrier, Some(Carrier::Assume | Carrier::Assert)))
        .collect();
    let unplaced = statements.iter().filter(|info| info.node.is_none()).count();
    let source_rows: Vec<_> =
        infos.iter().filter(|info| info.origin_kind == Some(OriginKind::Source)).collect();
    let unjoined = source_rows.iter().filter(|info| info.artifact.is_none()).count();
    // Aggregate slices use a function as their synthetic target while their
    // boundaries retain the actual terminal vertices. Any ungrounded boundary
    // therefore makes the aggregate ungrounded; comparing only with
    // `slice.target` silently reported vacuous functions as Grounded.
    let ungrounded =
        slice.boundaries.iter().any(|boundary| matches!(boundary, Boundary::Ungrounded { .. }));

    // Unlicensed exported assumptions this slice rests on. Counted over the
    // whole slice, not just statements, because any of them can be the reason
    // a supporting fact fell out.
    let unlicensed: Vec<&String> =
        slice.definite.iter().filter(|vertex| fail_open.contains(*vertex)).collect();

    serde_json::json!({
        "evidence": if slice.possible.is_empty() { "Measured" } else { "Overapproximated" },
        "grounding": if ungrounded { "Ungrounded" } else { "Grounded" },
        // The sixth dimension. Without it a slice resting on an unlicensed
        // export reports `Complete` and its findings look defensible.
        "licensing": {
            "status": if unlicensed.is_empty() { "Complete" } else { "Partial" },
            "unlicensed_roots": unlicensed.len(),
            "roots": unlicensed
                .iter()
                .map(|vertex| g.display(vertex))
                .collect::<BTreeSet<_>>(),
        },
        "attribution": {
            "status": if unresolved == 0 { "Complete" } else { "Partial" },
            "unresolved": unresolved,
        },
        "placement": {
            "status": if unplaced == 0 { "Complete" } else { "Partial" },
            "statement_occurrences": statements.len(),
            "missing": unplaced,
        },
        "artifact_projection": {
            "status": if unjoined == 0 { "Complete" } else { "Partial" },
            "source_occurrences": source_rows.len(),
            "missing": unjoined,
        },
    })
}

fn not_applicable_completeness() -> serde_json::Value {
    serde_json::json!({
        "evidence": "NotApplicable",
        "grounding": "NotEvaluated",
        "licensing": {"status": "NotEvaluated", "unlicensed_roots": 0, "roots": []},
        "attribution": {"status": "NotEvaluated", "unresolved": 0},
        "placement": {"status": "NotEvaluated", "statement_occurrences": 0, "missing": 0},
        "artifact_projection": {"status": "NotEvaluated", "source_occurrences": 0, "missing": 0},
    })
}

fn function_status(terminal_statuses: &BTreeMap<&'static str, usize>) -> &'static str {
    if terminal_statuses.len() == 1 && terminal_statuses.contains_key("NotApplicable") {
        "NotApplicable"
    } else if terminal_statuses.len() == 1 && terminal_statuses.contains_key("Ungrounded") {
        "Ungrounded"
    } else if terminal_statuses.contains_key("Overapproximated") {
        "Overapproximated"
    } else if terminal_statuses.contains_key("Partial")
        || terminal_statuses.contains_key("Ungrounded")
    {
        "Partial"
    } else {
        "Complete"
    }
}

fn boundary_json(boundary: &Boundary) -> serde_json::Value {
    match boundary {
        Boundary::Call { premise, caller, callee, cfg_node, call_artifact } => serde_json::json!({
            "kind": "opaque_call",
            "premise": premise,
            "caller": caller,
            "callee": callee,
            "cfg_node": cfg_node,
            "call_artifact": call_artifact,
        }),
        Boundary::Unmeasured { vertex, solver_context, terminal_path } => serde_json::json!({
            "kind": "unmeasured",
            "vertex": vertex,
            "solver_context": solver_context,
            "terminal_path": terminal_path,
        }),
        Boundary::TraitContract { artifact, trait_method, implementations } => serde_json::json!({
            "kind": "trait_contract",
            "artifact": artifact,
            "trait_method": trait_method,
            "implementations": implementations,
        }),
        Boundary::Ungrounded { vertex } => serde_json::json!({
            "kind": "ungrounded",
            "vertex": vertex,
        }),
    }
}

/// Whether a root premise is one the analysis is right to trust.
enum RootBucket {
    /// A base case of the grounding fixed point: the caller owes it, the
    /// trust base supplies it, it is control/data flow of this body, or it is
    /// a protocol's *hypothesis* (the `H` of a checked export), which nothing
    /// establishes by design.
    Expected,
    /// A construct with no licensing rule at all. Closing it means adding an
    /// identity, a protocol position, and a rule.
    NoRule,
    /// A modelled protocol's exported assumption that reached the graph as a
    /// root anyway: the rule exists, but its join did not fire for these rows.
    RuleDidNotFire,
    /// An encoding fact whose provenance is the lowering template only. No
    /// construct claims it, so no rule can license it; listed separately
    /// rather than assumed harmless.
    Untyped,
}

#[derive(Default)]
struct UnlicensedGroup {
    rows: usize,
    with_artifact: usize,
    with_node: usize,
    /// The emission role distinguishes the export from the check it depends on.
    positioned: bool,
    functions: BTreeSet<String>,
}

/// Group label for a root premise: the emission kind, plus the residual
/// intent where the role carries no finer position.
fn emission_group(emission: &record::EmissionRole) -> String {
    match emission {
        record::EmissionRole::Assumed { intent } => format!("assumed/{intent:?}"),
        other => other.phase().unwrap_or_else(|| format!("{other:?}")),
    }
}

/// Classify a root premise, and report whether its role carries a protocol
/// position.
///
/// Exhaustive over `EmissionRole` on purpose: a new role cannot be added
/// without deciding whether it is legitimately a root. A catch-all arm here
/// would silently classify the next unmodelled construct as trusted, which is
/// the failure this view exists to surface.
fn root_expectation(emission: &record::EmissionRole) -> (RootBucket, bool) {
    use record::EmissionRole as E;
    match emission {
        // The caller owes these; the trust base supplies these.
        E::FunctionRequires { .. } | E::UserAssumption => (RootBucket::Expected, true),
        // Control and data flow of this body.
        E::BranchCondition { .. }
        | E::LoopEntryCondition
        | E::LoopExitCondition
        | E::AssignmentEquality
        | E::MutationEquality
        | E::SsaReconciliation { .. }
        | E::PathTermination
        | E::StringLiteral => (RootBucket::Expected, true),
        // Encoding facts with no source subject and nothing to license.
        E::TypeInvariant { .. }
        | E::HasType
        | E::Resolution
        | E::MutRefCurrent
        | E::Fuel { .. }
        | E::TraitBound => (RootBucket::Expected, true),
        // A checked export's *hypothesis*: the `H` of the triple. Nothing
        // establishes a universally quantified bound variable or a lemma's
        // assumed precondition, so these are roots by design.
        E::AssertForall { point: record::ForallPoint::Hypothesis } => (RootBucket::Expected, true),
        // Exported assumptions of a modelled protocol. The rule exists, so a
        // root here means its join did not fire for this occurrence.
        E::LoopInvariant { .. }
        | E::Assertion { .. }
        | E::AssertQuery { .. }
        | E::AssertForall { .. }
        | E::CallPostcondition { .. } => (RootBucket::RuleDidNotFire, true),
        // The open assumption of an invariant block. Licensed by the block's
        // close obligation through the recorded checked export, so a root here
        // means the pairing was not recorded.
        E::InvariantBlock { .. } => (RootBucket::RuleDidNotFire, true),
        // No rule, and the role carries no protocol position either.
        E::Assumed { .. } => (RootBucket::NoRule, false),
        // Provenance is the lowering template only.
        E::Lowered { .. } => (RootBucket::Untyped, false),
        // Obligations. Never premises, so never roots; classified so the match
        // stays exhaustive.
        E::FunctionEnsures
        | E::CallPrecondition { .. }
        | E::TerminationCheck { .. }
        | E::DecreaseHeightCheck
        | E::ArithOverflowCheck
        | E::PatternMatchCheck => (RootBucket::Expected, true),
    }
}

/// What snapshot 1 recorded about a function, if anything. Absent for
/// functions the pre-simplified crate did not contain (older records, or
/// synthesized bodies).
fn source_function<'a>(
    records: &'a [CoverageRecord],
    record_index: usize,
    fun: &str,
) -> Option<&'a record::SourceFunction> {
    records.get(record_index)?.source_functions.iter().find(|f| f.fun == fun)
}

/// The report's projection of a source function: mode, kind, and trust.
fn source_function_json(sf: &record::SourceFunction) -> serde_json::Value {
    serde_json::json!({
        // Display name. `fun` on the enclosing row is the identity.
        "friendly": sf.friendly,
        "krate": sf.krate,
        "local": sf.local,
        "mode": sf.mode,
        "kind": sf.kind,
        "item": sf.item,
        "module": sf.module,
        "visibility": sf.visibility,
        "body_visibility": sf.body_visibility,
        "opaqueness": sf.opaqueness,
        "has_body": sf.has_body,
        "external_body": sf.external_body,
        "broadcast": sf.broadcast,
        "trusted": sf.trusted(),
        "span": sf.span,
    })
}

/// One-line study rendering of the same projection.
fn source_function_text(sf: &record::SourceFunction) -> String {
    let kind = match &sf.kind {
        record::FunctionKind::Static => "static".to_string(),
        record::FunctionKind::TraitMethodDecl { trait_path, has_default } => {
            format!("trait-method-decl:{trait_path}{}", if *has_default { "(default)" } else { "" })
        }
        record::FunctionKind::TraitMethodImpl { method, .. } => {
            format!("trait-method-impl:{method}")
        }
        record::FunctionKind::ForeignTraitMethodImpl { method, .. } => {
            format!("foreign-trait-method-impl:{method}")
        }
    };
    let mode = match sf.mode {
        record::FunctionMode::Spec => "spec",
        record::FunctionMode::Proof => "proof",
        record::FunctionMode::Exec => "exec",
    };
    let trust = if sf.external_body {
        "trusted(external_body)"
    } else if !sf.local {
        "imported"
    } else if !sf.has_body {
        "no-body"
    } else {
        "verified"
    };
    // Opaqueness governs a definition axiom, which only spec functions have.
    let opaque = match (sf.mode, &sf.opaqueness) {
        (record::FunctionMode::Spec, record::Opaqueness::Opaque) => " opaque",
        _ => "",
    };
    format!(
        "source mode={mode} kind={kind} {trust}{opaque}{}",
        if sf.broadcast { " broadcast" } else { "" }
    )
}

/// The source artifacts a slice touches: an occurrence's projected artifact,
/// or an artifact vertex itself. Decided by the graph's typed artifact set,
/// never by the spelling of a vertex.
fn projected_artifacts(g: &Graph, vertices: &BTreeSet<String>) -> Vec<String> {
    let mut artifacts = BTreeSet::new();
    for vertex in vertices {
        if let Some(artifact) = g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref()) {
            artifacts.insert(artifact.clone());
        } else if g.artifact_ids.contains(vertex) {
            artifacts.insert(vertex.clone());
        }
    }
    artifacts.into_iter().collect()
}

struct TargetRow {
    record_index: usize,
    query_id: u64,
    target: String,
    parent: Option<String>,
    fun: String,
    desc: String,
    span: String,
    terminal_path: Option<String>,
    shadow_result: Option<String>,
    evidence_measured: bool,
    target_observed: bool,
}

fn not_applicable(row: &TargetRow) -> bool {
    row.shadow_result.as_deref().is_some_and(|result| result.starts_with("canonical_"))
}

fn coverage_eligibility(row: &TargetRow) -> &'static str {
    if not_applicable(row) {
        "not-applicable"
    } else if !row.evidence_measured {
        "unmeasured"
    } else if row.target_observed {
        "eligible"
    } else {
        "vacuous"
    }
}

fn query_evidence_measured(query: &proof_coverage::record::QueryRecord) -> bool {
    query.shadow_result.as_deref() == Some("valid")
        && matches!(
            query.evidence_backend.as_deref(),
            Some("unsat_core" | "proof_enabled_unsat_core")
        )
        && query.core.is_some()
}

fn targets(records: &[CoverageRecord]) -> Vec<TargetRow> {
    let multi = records.len() > 1;
    let mut out = Vec::new();
    for (record_index, record) in records.iter().enumerate() {
        let ns = |label: &str| {
            if multi { format!("r{}%{}", record_index, label) } else { label.to_string() }
        };
        for query in &record.queries {
            if query.family != QueryFamily::Focused {
                continue;
            }
            let Some(target) = &query.target_label else { continue };
            let evidence_measured = query_evidence_measured(query);
            out.push(TargetRow {
                record_index,
                query_id: query.id,
                target: ns(target),
                parent: query.parent_obligation_label.as_deref().map(&ns),
                fun: query.fun.clone(),
                desc: query.desc.clone(),
                span: query.span.clone(),
                terminal_path: query.terminal_path.clone(),
                shadow_result: query.shadow_result.clone(),
                evidence_measured,
                target_observed: evidence_measured
                    && query
                        .core
                        .as_ref()
                        .is_some_and(|core| core.iter().any(|label| label == target)),
            });
        }
    }
    out.sort_by(|a, b| {
        (&a.fun, &a.parent, &a.terminal_path, &a.target).cmp(&(
            &b.fun,
            &b.parent,
            &b.terminal_path,
            &b.target,
        ))
    });
    out
}

/// Research-facing name for a relation. Exhaustive: the weak kinds keep their
/// raw spelling, which is what the previous fallthrough produced.
fn research_relation(kind: analysis::ArcKind) -> &'static str {
    match kind {
        analysis::ArcKind::SupportedBy => "support-witness",
        analysis::ArcKind::TerminalOf => "terminal-group",
        analysis::ArcKind::CertifiedBy => "certificate",
        analysis::ArcKind::Aggregates => "aggregate",
        analysis::ArcKind::Demand => "demand-refined-call",
        weak @ (analysis::ArcKind::ObservedInBatch | analysis::ArcKind::ElaboratesTo) => {
            weak.as_str()
        }
    }
}

fn focused_evidence(records: &[CoverageRecord], row: &TargetRow) -> Option<BTreeSet<String>> {
    if !row.evidence_measured {
        return None;
    }
    let query = records[row.record_index]
        .queries
        .iter()
        .find(|query| query.id == row.query_id && query.family == QueryFamily::Focused)?;
    let target = query.target_label.as_deref()?;
    let namespace = |label: &str| {
        if records.len() > 1 {
            format!("r{}%{}", row.record_index, label)
        } else {
            label.to_string()
        }
    };
    Some(
        query
            .core
            .as_ref()?
            .iter()
            .filter(|label| label.as_str() != target)
            .map(|label| namespace(label))
            .collect(),
    )
}

fn research_vertex_class(g: &Graph, vertex: &str) -> &'static str {
    if g.background_roots.contains(vertex) {
        "background"
    } else if g.ambient_owner.contains_key(vertex) {
        "ambient"
    } else if g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref()).is_some() {
        "source"
    } else {
        "generated"
    }
}

fn print_research_set(label: &str, vertices: &BTreeSet<String>, g: &Graph) {
    println!("  {label}={{");
    for vertex in vertices {
        println!("    {}", g.display_friendly(vertex));
    }
    println!("  }}");
}

fn print_query_findings(g: &Graph, findings: &[QueryFinding], target: &str) {
    for finding in findings {
        match finding {
            QueryFinding::UncoveredPremise { source, terminal, .. }
                if terminal.terminal_ref == target =>
            {
                // A query-scope statement, not a finding: the fact was in
                // this one query's validated scope and absent from this one
                // witness. It becomes a finding only if it survives
                // root-scoping at function level.
                println!(
                    "observation available-not-observed artifact={}",
                    g.display_artifact(&source.artifact)
                );
            }
            QueryFinding::VacuousObligation { source, terminal, .. }
                if terminal.terminal_ref == target =>
            {
                // Vacuity is a finding at query scope too: it is measured from
                // this terminal's own core, so it needs no root-scoping. It
                // carries the same §2.1 subtype as at function scope.
                let phase = terminal
                    .parent_obligation_ref
                    .as_deref()
                    .and_then(|p| g.vertex_info.get(p))
                    .and_then(|info| info.phase.clone());
                println!(
                    "finding {} artifact={}",
                    vacuous_subtype(terminal.artifact_kind.as_ref(), phase.as_deref()),
                    source
                        .as_ref()
                        .map(|source| g.display_artifact(&source.artifact))
                        .unwrap_or_else(|| "-".to_string())
                );
            }
            _ => {}
        }
    }
}

/// Function-scope findings, relative to the selected roots.
///
/// The candidate population is every `available-not-observed` observation
/// made by a measured terminal of this function — not only the roots' own
/// queries. A loop body lowered into its own query is reached by a
/// postcondition root only through the loop certificate, so a body fact the
/// roots never reach would otherwise not even be a candidate. A candidate
/// survives when its artifact is absent from every root's direct and
/// transitive slice; observation by a non-root terminal qualifies it as
/// auxiliary support and never suppresses it. Vacuity remains a statement
/// about a root terminal itself.
fn print_function_findings(
    g: &Graph,
    findings: &[QueryFinding],
    roots: &BTreeSet<String>,
    covered_artifacts: &BTreeSet<String>,
    aux_support: &BTreeMap<String, Vec<String>>,
    record_index: usize,
    function: &str,
    gate: &WeakCouplingGate,
) {
    // artifact (display id) -> (namespaced key, artifact kind)
    let mut uncovered: BTreeMap<String, (String, record::ArtifactKind)> = BTreeMap::new();
    let mut vacuous: BTreeMap<String, &'static str> = BTreeMap::new();
    for finding in findings {
        match finding {
            QueryFinding::UncoveredPremise { source, terminal, .. }
                if terminal.record_index == record_index && terminal.function == function =>
            {
                let key = g.artifact_vertex(source.record_index, &source.artifact);
                if !covered_artifacts.contains(&key) {
                    uncovered.insert(source.artifact.clone(), (key, source.artifact_kind.clone()));
                }
            }
            QueryFinding::VacuousObligation { source, terminal, .. }
                if roots.contains(&terminal.terminal_ref) =>
            {
                let subject = source
                    .as_ref()
                    .map(|source| source.artifact.clone())
                    .unwrap_or_else(|| terminal.terminal_ref.clone());
                let phase = terminal
                    .parent_obligation_ref
                    .as_deref()
                    .and_then(|p| g.vertex_info.get(p))
                    .and_then(|info| info.phase.clone());
                vacuous.insert(
                    subject,
                    vacuous_subtype(terminal.artifact_kind.as_ref(), phase.as_deref()),
                );
            }
            _ => {}
        }
    }
    // Same vocabulary and same precedence as `rooted_json`; §7 requires the
    // text view and the report's `rooted` section not to drift.
    for (artifact, (key, kind)) in uncovered {
        let aux = aux_support.get(&key);
        if program_fact(&kind) && !gate.open() {
            continue;
        }
        let finding_kind = if context_family(&kind) {
            "unobserved-context"
        } else if aux.is_some_and(|notes| !notes.is_empty()) {
            "auxiliary-only-fact"
        } else if protocol_bearing(&kind) {
            "checked-but-unused-proof-step"
        } else if program_fact(&kind) {
            "goal-disconnected-code"
        } else {
            unused_subtype(&kind)
        };
        println!("finding {finding_kind} artifact={}", g.display_artifact(&artifact));
        for note in aux.into_iter().flatten() {
            println!("  auxiliary-support {note}");
        }
    }
    for (artifact, kind) in vacuous {
        println!("finding {kind} artifact={}", g.display_artifact(&artifact));
    }
}

/// One measured root witness: the atomic focused core of a selected root,
/// kept as a set. Consumers must not flatten it into pairwise edges.
struct RootedWitness {
    query_id: u64,
    root: String,
    observed: bool,
    members: BTreeSet<String>,
}

/// Root-scoped function results shared by the study text view and the JSON
/// report. Roots are the selected terminals (postconditions by default);
/// every set is derived from their witnesses and productive slices only.
struct RootedData<'a> {
    roots: Vec<&'a TargetRow>,
    direct_support: BTreeSet<String>,
    direct_contradiction: BTreeSet<String>,
    transitive: BTreeSet<String>,
    generated_support: BTreeSet<String>,
    ambient_support: BTreeSet<String>,
    boundaries: BTreeSet<Boundary>,
    steps: BTreeSet<SliceStep>,
    covered_artifacts: BTreeSet<String>,
    witnesses: Vec<RootedWitness>,
    /// namespaced artifact -> measured observed non-root terminals in the
    /// same function scope whose witnesses contain that artifact.
    aux_rows: BTreeMap<String, Vec<&'a TargetRow>>,
    /// premise vertices at opaque call boundaries (imported locality).
    imported: BTreeSet<String>,
}

fn rooted_data<'a>(
    g: &Graph,
    records: &[CoverageRecord],
    all_targets: &'a [TargetRow],
    record_index: usize,
    function: &str,
    rows: &[(&'a TargetRow, Option<Slice>)],
) -> RootedData<'a> {
    let roots: Vec<&TargetRow> = rows.iter().map(|(row, _)| *row).collect();
    let root_targets: BTreeSet<String> = roots.iter().map(|row| row.target.clone()).collect();
    let mut direct_support = BTreeSet::new();
    let mut direct_contradiction = BTreeSet::new();
    let mut generated_support = BTreeSet::new();
    let mut ambient_support = BTreeSet::new();
    let mut all_source = BTreeSet::new();
    let mut boundaries = BTreeSet::new();
    let mut steps = BTreeSet::new();
    let mut witnesses = Vec::new();
    let mut imported = BTreeSet::new();
    for (row, slice) in rows {
        if let Some(witness) = focused_evidence(records, row) {
            witnesses.push(RootedWitness {
                query_id: row.query_id,
                root: row.target.clone(),
                observed: row.target_observed,
                members: witness.clone(),
            });
            let (source_witness, other): (BTreeSet<String>, BTreeSet<String>) =
                witness.into_iter().partition(|vertex| {
                    g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref()).is_some()
                });
            if row.target_observed {
                direct_support.extend(source_witness);
                for vertex in other {
                    match research_vertex_class(g, &vertex) {
                        "generated" => {
                            generated_support.insert(vertex);
                        }
                        "ambient" => {
                            ambient_support.insert(vertex);
                        }
                        _ => {}
                    }
                }
            } else {
                direct_contradiction.extend(source_witness);
            }
        }
        let Some(slice) = slice else { continue };
        all_source.extend(
            slice
                .definite
                .iter()
                .filter(|vertex| {
                    g.vertex_info.get(*vertex).and_then(|info| info.artifact.as_ref()).is_some()
                })
                .cloned(),
        );
        for boundary in &slice.boundaries {
            if let Boundary::Call { premise, .. } = boundary {
                imported.insert(premise.clone());
            }
            boundaries.insert(boundary.clone());
        }
        steps.extend(slice.steps.iter().cloned());
    }
    let direct: BTreeSet<String> = direct_support.union(&direct_contradiction).cloned().collect();
    all_source.extend(direct.iter().cloned());
    let transitive: BTreeSet<String> = all_source.difference(&direct).cloned().collect();
    let covered_artifacts: BTreeSet<String> = all_source
        .iter()
        .filter_map(|vertex| {
            g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref()).cloned()
        })
        .collect();

    // Auxiliary support: measured observed non-root terminals in this
    // function scope whose witnesses contain a source artifact. These
    // qualify available-not-observed findings: the fact supports an
    // auxiliary obligation while remaining outside every selected root's
    // slice. This is a per-terminal witness statement, not a necessity
    // claim.
    let mut aux_rows: BTreeMap<String, Vec<&TargetRow>> = BTreeMap::new();
    for row in all_targets {
        if row.record_index != record_index || row.fun != function {
            continue;
        }
        if root_targets.contains(&row.target) || !row.target_observed {
            continue;
        }
        let Some(witness) = focused_evidence(records, row) else { continue };
        let witness_artifacts: BTreeSet<String> = witness
            .iter()
            .filter_map(|vertex| {
                g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref()).cloned()
            })
            .collect();
        for artifact in witness_artifacts {
            aux_rows.entry(artifact).or_default().push(row);
        }
    }

    RootedData {
        roots,
        direct_support,
        direct_contradiction,
        transitive,
        generated_support,
        ambient_support,
        boundaries,
        steps,
        covered_artifacts,
        witnesses,
        aux_rows,
        imported,
    }
}

/// Serialize root-scoped function results into the report contract. Every
/// set keeps vertex refs as opaque join keys; display metadata is carried in
/// the `vertices` table so consumers never parse refs or reconstruct
/// coverage from raw cores.
/// Source families that carry a checked-export protocol. An unused export
/// from one of these is verified-but-unreached proof scaffolding rather than
/// a plain unused hypothesis, which `PROOF_COVERAGE_FINDINGS.md` §2.3 names
/// `checked-but-unused-proof-step`.
fn protocol_bearing(kind: &record::ArtifactKind) -> bool {
    use record::ArtifactKind as K;
    matches!(kind, K::Assertion | K::AssertForall | K::LoopInvariantClause | K::LemmaEnsuresClause)
}

/// Whether every selected root was discharged by contradictory context.
///
/// An absence relative only to vacuous roots is not useful evidence that a
/// proof fact is unnecessary: there is no supported proof argument for it to
/// participate in. Such rows remain available as secondary observations, but
/// are not promoted to findings.
fn all_roots_vacuous(data: &RootedData<'_>) -> bool {
    !data.roots.is_empty() && data.roots.iter().all(|row| !row.target_observed)
}

fn mixed_root_vacuity(data: &RootedData<'_>) -> bool {
    data.roots.iter().any(|row| row.target_observed)
        && data.roots.iter().any(|row| !row.target_observed)
}

/// Relevant completeness dimensions for a finding derived by subtracting a
/// root slice. Positive reachability and terminal-core findings do not use
/// this predicate.
fn absence_evidence_complete(completeness: &serde_json::Value) -> bool {
    completeness.get("evidence").and_then(|v| v.as_str()) == Some("Measured")
        && completeness.get("grounding").and_then(|v| v.as_str()) == Some("Grounded")
        // Placement and artifact-projection gaps remain diagnostics, but do
        // not blanket-withhold a named fact. Licensing can actually drop its
        // support from the slice; unresolved attribution can make the
        // observed argument unknown. Artifact-family occlusion is handled on
        // the individual row.
        && ["licensing", "attribution"].into_iter().all(|dimension| {
            completeness.get(dimension).and_then(|v| v.get("status")).and_then(|v| v.as_str())
                == Some("Complete")
        })
}

fn secondary_observation(mut row: serde_json::Value, reason: &'static str) -> serde_json::Value {
    if let Some(obj) = row.as_object_mut() {
        obj.insert("disposition".into(), serde_json::json!("secondary"));
        obj.insert("secondary_reason".into(), serde_json::json!(reason));
        obj.insert("presentation".into(), serde_json::json!("information"));
        // A secondary observation is intentionally not assigned a
        // defensibility/action verdict. Its underlying evidence remains in
        // query observations and the rooted classification.
        obj.remove("defensible");
        obj.remove("withheld_reason");
    }
    row
}

enum AssumptionSource {
    Explicit(&'static str),
    OtherSourceConstruct,
    Unavailable,
}

/// `UserAssumption` is also used by macro-generated state-machine hypotheses
/// such as `require`, `remove`, and `have`. Those are protocol premises, not
/// unchecked source trust. Until the record gives them a distinct typed role,
/// use the exact source span to retain only explicit `assume`/`admit` syntax.
/// If source is unavailable, fail conservatively and keep the trust row.
fn assumption_source(span: Option<&str>) -> AssumptionSource {
    let Some((path, line, _)) = span.and_then(span_location) else {
        return AssumptionSource::Unavailable;
    };
    let Ok(source) = std::fs::read_to_string(path) else {
        return AssumptionSource::Unavailable;
    };
    let Some(line) = source.lines().nth(line.saturating_sub(1)) else {
        return AssumptionSource::Unavailable;
    };
    let code = line.split("//").next().unwrap_or(line);
    if code.contains("admit(") || code.contains("admit()") {
        AssumptionSource::Explicit("admission")
    } else if code.contains("assume(") {
        AssumptionSource::Explicit("user-assumption")
    } else {
        AssumptionSource::OtherSourceConstruct
    }
}

/// Installed proof context: ambient axioms, broadcast lemmas, reveals,
/// specification definitions. §2.6 is explicit that core absence for these
/// supports only `unobserved-context`, never a removability claim.
fn context_family(kind: &record::ArtifactKind) -> bool {
    matches!(kind, record::ArtifactKind::Reveal)
}

/// Implementation facts, as opposed to specifications. §2.5 makes these
/// `goal-disconnected-code` — and only for executable functions with a
/// visible body and declared goals; elsewhere they stay coverage data.
fn program_fact(kind: &record::ArtifactKind) -> bool {
    use record::ArtifactKind as K;
    matches!(kind, K::Assignment | K::BranchCondition | K::ReturnBinding | K::LoopCondition)
}

/// §2.2: refine an unused specification fact by its artifact family. Match is
/// exhaustive so a new `ArtifactKind` forces a decision here rather than
/// silently falling into the program-fact bucket.
fn unused_subtype(kind: &record::ArtifactKind) -> &'static str {
    use record::ArtifactKind as K;
    match kind {
        K::RequiresClause | K::RequiresAggregate | K::LemmaRequiresClause => {
            "goal-unused-precondition"
        }
        K::LoopInvariantClause => "goal-unused-loop-invariant",
        K::Assertion | K::AssertForall => "goal-unused-assertion",
        K::LemmaEnsuresClause | K::LocalLemma => "goal-unused-local-lemma",
        K::Assumption => "goal-unused-assumption",
        K::EnsuresClause | K::EnsuresAggregate => "goal-unused-callee-contract",
        K::Reveal => "unobserved-context",
        K::Assignment
        | K::BranchCondition
        | K::ReturnBinding
        | K::LoopCondition
        | K::CallSite
        | K::Function
        | K::DecreasesAggregate
        | K::DecreasesClause => "goal-unused-program-fact",
    }
}

/// §2.1: retain the obligation kind on a vacuous goal. `phase` disambiguates
/// loop establishment from maintenance when the record carries it. A terminal
/// with no artifact keeps the generic kind.
fn vacuous_subtype(kind: Option<&record::ArtifactKind>, phase: Option<&str>) -> &'static str {
    use record::ArtifactKind as K;
    match kind {
        Some(K::EnsuresClause) | Some(K::EnsuresAggregate) => "vacuous-postcondition",
        Some(K::Assertion) | Some(K::AssertForall) => "vacuous-assertion",
        Some(K::RequiresClause) | Some(K::RequiresAggregate) => "vacuous-call-precondition",
        Some(K::LoopInvariantClause) => match phase {
            Some(p) if p.contains("establish") => "vacuous-loop-establishment",
            _ => "vacuous-loop-maintenance",
        },
        Some(K::DecreasesAggregate) | Some(K::DecreasesClause) => "vacuous-termination-check",
        _ => "vacuous-goal",
    }
}

/// Inputs to the §2.5 weak-coupling gate, decided per function from
/// snapshot-1 metadata. Both weak-coupling findings are suppressed unless all
/// of these hold, so proof/spec functions and executable functions without
/// declared goals contribute coverage data but no such finding.
struct WeakCouplingGate {
    executable: bool,
    has_body: bool,
    body_visible: bool,
    external_body: bool,
    has_declared_goals: bool,
}

/// The §2.5 gate for the study text path. `roots` is the study's selected root
/// set, so an empty one means no declared goals were selected here either.
fn study_gate(
    records: &[CoverageRecord],
    record_index: usize,
    function: &str,
    roots: &BTreeSet<String>,
) -> WeakCouplingGate {
    let sf = source_function(records, record_index, function);
    WeakCouplingGate {
        executable: sf.is_some_and(|f| f.mode == record::FunctionMode::Exec),
        has_body: sf.is_some_and(|f| f.has_body),
        body_visible: sf
            .is_some_and(|f| matches!(f.body_visibility, record::BodyVisibility::Visible { .. })),
        external_body: sf.is_none_or(|f| f.external_body),
        has_declared_goals: !roots.is_empty(),
    }
}

impl WeakCouplingGate {
    fn open(&self) -> bool {
        self.executable
            && self.has_body
            && self.body_visible
            && !self.external_body
            && self.has_declared_goals
    }
}

fn rooted_json(
    g: &Graph,
    records: &[CoverageRecord],
    data: &RootedData,
    query_findings: &[QueryFinding],
    record_index: usize,
    function: &str,
    record_count: usize,
    policy: &'static str,
    // Which obligations were selected as roots, and why. `declared-goals` is
    // the default; `all-measured` is the no-declared-goals fallback, under
    // which a finding reads "unused by all measured obligations" rather than
    // "unused by declared goals"; `none` selects nothing and emits no
    // findings. See the root-selection comment at the call site.
    root_policy: &'static str,
    root_reason: Option<&'static str>,
    // How a finding under this root set must be read, carried onto each row.
    relation: &'static str,
    // §2.5 gate for the two weak-coupling findings.
    gate: &WeakCouplingGate,
    // Completeness over the selected roots only — the scope a finding is
    // relative to, and therefore the scope its defensibility is decided in.
    rooted_completeness: &serde_json::Value,
    // `occluded_details`: origin details of source-like evidence in this
    // function scope that carries no artifact. A verdict about an artifact of
    // the same family cannot be claimed while such evidence exists, so it is
    // reported `occluded`: the unidentified rows could be this very clause at
    // another protocol position.
    occluded_details: &BTreeSet<String>,
) -> serde_json::Value {
    let de_ns = |value: &str| -> String {
        if record_count > 1 {
            value.strip_prefix(&format!("r{record_index}%")).unwrap_or(value).to_string()
        } else {
            value.to_string()
        }
    };
    let vertex_json = |vertex: &str| -> serde_json::Value {
        if let Some(owner) = g.ambient_owner.get(vertex) {
            return serde_json::json!({
                "class": "ambient",
                "owner": owner,
                "op": g.ambient_op.get(vertex),
            });
        }
        let info = g.vertex_info.get(vertex);
        serde_json::json!({
            "class": research_vertex_class(g, vertex),
            "artifact": info.and_then(|info| info.artifact.as_deref()).map(&de_ns),
            "origin": info.map(|info| {
                info.origin_kind.map(|kind| kind.to_string()).unwrap_or_default()
            }),
            "detail": info.map(|info| info.detail.clone()),
            "phase": info.and_then(|info| info.phase.clone()),
            "span": info.and_then(|info| info.span.clone()),
            "role": info.map(|info| info.role.map(|role| role.to_string()).unwrap_or_default()),
            "unresolved": info.map(|info| info.unresolved).unwrap_or(false),
        })
    };
    let roots_set: BTreeSet<String> = data.roots.iter().map(|row| row.target.clone()).collect();
    let selected_root_artifacts: BTreeSet<String> = data
        .roots
        .iter()
        .filter_map(|row| {
            row.parent
                .as_deref()
                .and_then(|parent| g.vertex_info.get(parent))
                .and_then(|info| info.artifact.clone())
        })
        .collect();
    let every_root_vacuous = all_roots_vacuous(data);
    let some_roots_vacuous = mixed_root_vacuity(data);
    let effective_relation = match (root_policy, some_roots_vacuous) {
        ("declared-goals", true) => "unused by all non-vacuous declared goals",
        ("all-measured", true) => "unused by all non-vacuous measured obligations",
        _ => relation,
    };

    // Per-artifact classification with per-class occurrence refs. The
    // strongest class orders source presentation; refs stay lossless.
    let mut classes: BTreeMap<String, BTreeMap<&'static str, BTreeSet<String>>> = BTreeMap::new();
    for (set, class) in [
        (&data.direct_support, "direct-support"),
        (&data.direct_contradiction, "direct-contradiction"),
        (&data.transitive, "transitive"),
    ] {
        for vertex in set {
            if let Some(artifact) =
                g.vertex_info.get(vertex).and_then(|info| info.artifact.as_ref())
            {
                classes
                    .entry(artifact.clone())
                    .or_default()
                    .entry(class)
                    .or_default()
                    .insert(vertex.clone());
            }
        }
    }
    let classification: Vec<serde_json::Value> = classes
        .iter()
        .map(|(artifact_ns, class_refs)| {
            let raw = de_ns(artifact_ns);
            let strongest = ["direct-support", "direct-contradiction", "transitive"]
                .into_iter()
                .find(|class| class_refs.contains_key(class))
                .unwrap_or("transitive");
            // Materialized artifact verdict relative to the selected roots.
            // goal-supporting: in some root's direct or transitive slice;
            // contradiction: source evidence of a vacuous root's witness.
            let verdict = if strongest == "direct-contradiction"
                && !class_refs.contains_key("direct-support")
                && !class_refs.contains_key("transitive")
            {
                "contradiction"
            } else {
                "goal-supporting"
            };
            let locality =
                if class_refs.values().flatten().any(|vertex| data.imported.contains(vertex)) {
                    "imported"
                } else {
                    "local"
                };
            let meta = records[record_index].artifacts.iter().find(|a| a.id == raw);
            serde_json::json!({
                "artifact": raw,
                "record_index": record_index,
                "artifact_kind": meta.map(|a| a.kind.clone()),
                "owner": meta.map(|a| a.owner.clone()),
                "span": meta.and_then(|a| a.span.clone()),
                "class": strongest,
                "verdict": verdict,
                "locality": locality,
                "classes": class_refs,
            })
        })
        .collect();

    // Root-scoped findings, mirroring the study text: an artifact is
    // available-not-observed only when absent from every selected root's
    // direct and transitive slice; auxiliary support qualifies but never
    // suppresses. Vacuous roots keep their own finding.
    let aux_json = |key: &str| -> Vec<serde_json::Value> {
        data.aux_rows
            .get(key)
            .map(|rows| {
                rows.iter()
                    .map(|row| {
                        let parent_info =
                            row.parent.as_deref().and_then(|parent| g.vertex_info.get(parent));
                        serde_json::json!({
                            "terminal": row.target,
                            "parent": row.parent,
                            "query_id": row.query_id,
                            "obligation_detail": parent_info.map(|info| info.detail.clone()),
                            "span": parent_info
                                .and_then(|info| info.span.clone())
                                .unwrap_or_else(|| row.span.clone()),
                        })
                    })
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut uncovered: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    let mut vacuous: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    let mut secondary: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    let mut vacuous_subjects: BTreeSet<String> = BTreeSet::new();
    // Non-root vacuity of extent `some`: an infeasible path, reported
    // separately and collapsed by default. It is real information — that branch
    // is dead — but it is not a defect and it would swamp the finding list.
    let mut infeasible: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    // Every finding below is root-relative and witness-relative
    // (`PROOF_COVERAGE_FINDINGS.md` §1). Candidates are every measured
    // terminal's observations in this function scope; survivors are those
    // outside every root slice. When `root_policy` is `none` no root was
    // selected, so there is nothing to be outside of and no finding is made.
    if root_policy != "none" {
        for finding in query_findings {
            match finding {
                QueryFinding::UncoveredPremise { source, terminal, .. }
                    if terminal.record_index == record_index && terminal.function == function =>
                {
                    let key = g.artifact_vertex(source.record_index, &source.artifact);
                    if data.covered_artifacts.contains(&key) {
                        continue;
                    }
                    let kind = &source.artifact_kind;
                    // §2.5: implementation facts are a weak-coupling finding
                    // and only for executable functions with a visible body
                    // and declared goals. Otherwise they are coverage data,
                    // not a finding, and are dropped here rather than retyped.
                    if program_fact(kind) && !gate.open() {
                        continue;
                    }
                    let aux = aux_json(&key);
                    // `occluded` withholds a verdict when unidentified source
                    // evidence of the same family exists in this scope: those
                    // rows could be this very clause at another protocol
                    // position.
                    let family = match kind {
                        record::ArtifactKind::LoopInvariantClause => Some("loop_invariant"),
                        record::ArtifactKind::EnsuresClause => Some("ensures"),
                        record::ArtifactKind::Assertion => Some("assertion"),
                        _ => None,
                    };
                    let occluded = family.is_some_and(|f| occluded_details.contains(f));
                    // Specializations are emitted *instead of* the generic
                    // unused-fact kind, never alongside it. Precedence:
                    // installed context (§2.6) → observed by a non-root
                    // obligation (§2.2) → discharged protocol export (§2.3) →
                    // implementation fact (§2.5) → generic family (§2.2).
                    let finding_kind = if context_family(kind) {
                        "unobserved-context"
                    } else if !aux.is_empty() {
                        "auxiliary-only-fact"
                    } else if protocol_bearing(kind) {
                        "checked-but-unused-proof-step"
                    } else if program_fact(kind) {
                        "goal-disconnected-code"
                    } else {
                        unused_subtype(kind)
                    };
                    uncovered.entry(source.artifact.clone()).or_insert_with(|| {
                        serde_json::json!({
                            "kind": finding_kind,
                            // What sort of claim this is, independent of the
                            // §2 subtype: an *absence* claim is derived by
                            // subtracting a slice and so is what a licensing
                            // hole can invalidate. Consumers key severity and
                            // defensibility off this, not off the subtype.
                            "claim": "absence",
                            // How the row was derived, which is what decides
                            // whether a licensing hole can invalidate it.
                            // `claim` is for rendering and severity; this is
                            // for defensibility. They are not the same axis:
                            // `goal-without-body-support` renders as coupling
                            // but is derived by absence.
                            "evidence_basis": "slice-absence",
                            "family": unused_subtype(kind),
                            "verdict": if occluded { "occluded" } else { "unlinked" },
                            "root_policy": root_policy,
                            "finding_relation": effective_relation,
                            "presentation": if finding_kind == "auxiliary-only-fact" {
                                "information"
                            } else {
                                "review"
                            },
                            "source": source,
                            "auxiliary_support": aux,
                            // §4/§7: core absence is not removability. Set
                            // only by a recorded confirmation mutation.
                            "counterfactual_checked": false,
                        })
                    });
                }
                QueryFinding::VacuousObligation { source, terminal, .. }
                    if terminal.record_index == record_index && terminal.function == function =>
                {
                    // Vacuity is direct terminal evidence, so it is not gated
                    // on root selection the way an absence claim must be.
                    // Strict root filtering would delete every subtype except
                    // `vacuous-postcondition` from any function that has a
                    // postcondition. Instead the row records its relation to
                    // the root set and the caller decides:
                    //
                    //   selected-root                  → finding, any extent
                    //   non-root, extent = all         → auxiliary finding:
                    //                                    that obligation is
                    //                                    not proved at all
                    //   non-root, extent = some        → infeasible-path
                    //                                    observation, collapsed
                    //
                    // §2.1 extent: does the contradiction discharge every
                    // terminal of this obligation, or only some paths? "all"
                    // means nothing about the obligation is proved; "some"
                    // means the vacuous terminals are infeasible branches,
                    // which is what `assert(false)` and
                    // `assert_by_contradiction!` produce by design.
                    let parent = terminal.parent_obligation_ref.as_deref();
                    let root_relation = if roots_set.contains(&terminal.terminal_ref) {
                        "selected-root"
                    } else {
                        "non-root"
                    };
                    let phase = parent
                        .and_then(|p| g.vertex_info.get(p))
                        .and_then(|info| info.phase.clone());
                    // Extent is measured over the *source artifact*, not over
                    // one obligation occurrence. A clause checked on several
                    // paths gets one obligation occurrence per path, so a
                    // per-occurrence extent is always `all` and answers
                    // nothing. The question worth asking is "is this clause
                    // proved anywhere?", which spans every obligation carrying
                    // the artifact.
                    let obligation_labels: BTreeSet<&str> = match source.as_ref() {
                        Some(source) => records[record_index]
                            .queries
                            .iter()
                            .flat_map(|q| q.occurrences.iter())
                            .filter(|o| {
                                o.role == record::Role::Obligation
                                    && o.artifact.as_deref() == Some(source.artifact.as_str())
                            })
                            .filter_map(|o| o.label.as_deref())
                            .collect(),
                        None => parent
                            .map(|p| p.strip_prefix(&format!("r{record_index}%")).unwrap_or(p))
                            .into_iter()
                            .collect(),
                    };
                    let (total, vacuous_count) = Some(&obligation_labels)
                        .filter(|labels| !labels.is_empty())
                        .map(|labels| {
                            let queries = records[record_index].queries.iter().filter(|q| {
                                q.parent_obligation_label
                                    .as_deref()
                                    .is_some_and(|l| labels.contains(l))
                            });
                            let total = queries.clone().count();
                            // Vacuous: measured, and the terminal's own label
                            // is absent from the accepted core.
                            let vac = queries
                                .filter(|q| {
                                    query_evidence_measured(q)
                                        && match (&q.core, q.target_label.as_deref()) {
                                            (Some(core), Some(target)) => {
                                                !core.iter().any(|l| l == target)
                                            }
                                            _ => false,
                                        }
                                })
                                .count();
                            (total, vac)
                        })
                        .unwrap_or((1, 1));
                    let extent = if total > 0 && vacuous_count >= total { "all" } else { "some" };
                    // Keyed on the subject the extent is measured over: the
                    // artifact when there is one, else the parent obligation.
                    // Keying on the terminal produced one row per dead path,
                    // each claiming the same extent; keying on the obligation
                    // occurrence still produced one row per path, because a
                    // clause checked on several paths has one occurrence each.
                    let key = source
                        .as_ref()
                        .map(|source| source.artifact.clone())
                        .or_else(|| parent.map(str::to_string))
                        .unwrap_or_else(|| terminal.terminal_ref.clone());
                    vacuous_subjects.insert(key.clone());
                    let kind = vacuous_subtype(terminal.artifact_kind.as_ref(), phase.as_deref());
                    let row = serde_json::json!({
                        "kind": if root_relation == "selected-root" {
                            kind
                        } else if extent == "some" {
                            "infeasible-path"
                        } else {
                            kind
                        },
                        "claim": "vacuity",
                        // Read straight off the terminal's own core: the
                        // terminal was absent from its own witness. No slice
                        // subtraction, so no licensing hole reaches it.
                        "evidence_basis": "terminal-core",
                        "family": "vacuous-goal",
                        "root_relation": root_relation,
                        // "all": contradictory context discharged every
                        // terminal. "some": the other terminals have supported
                        // proofs and these terminals are infeasible paths.
                        "extent": extent,
                        "vacuous_terminals": vacuous_count,
                        "obligation_terminals": total,
                        "root_policy": root_policy,
                        "presentation": if root_relation == "selected-root" && extent == "all" {
                            "warning"
                        } else {
                            "information"
                        },
                        "source": source,
                        "terminal": terminal,
                    });
                    if root_relation == "selected-root" {
                        vacuous.entry(key).or_insert(row);
                    } else if extent == "some" {
                        infeasible.entry(key).or_insert(row);
                    } else {
                        secondary
                            .entry(format!("vacuity:{key}"))
                            .or_insert_with(|| secondary_observation(row, "non-root-vacuity"));
                    }
                }
                _ => {}
            }
        }
    }

    // Cross-finding precedence and root intent:
    //
    // * If every selected root is vacuous, slice absence is downstream of the
    //   contradiction and is not promoted.
    // * A proof step cannot simultaneously be called vacuous and
    //   checked-but-unused.
    // * Under the no-declared-goals fallback, an assertion/lemma whose own
    //   check is a selected root is a standalone proof obligation. Its export
    //   may reach nothing later, but that does not make the assertion itself
    //   unnecessary.
    let mut primary_uncovered = BTreeMap::new();
    for (subject, row) in uncovered {
        let kind = row
            .get("source")
            .and_then(|source| source.get("artifact_kind"))
            .and_then(|kind| serde_json::from_value::<record::ArtifactKind>(kind.clone()).ok());
        let reason = if every_root_vacuous {
            Some("all-selected-roots-vacuous")
        } else if vacuous_subjects.contains(&subject) {
            Some("same-subject-vacuity")
        } else if root_policy == "all-measured"
            && selected_root_artifacts.contains(&subject)
            && kind.as_ref().is_some_and(protocol_bearing)
        {
            Some("selected-root-is-own-proof-obligation")
        } else {
            None
        };
        if let Some(reason) = reason {
            secondary.insert(format!("absence:{subject}"), secondary_observation(row, reason));
        } else {
            primary_uncovered.insert(subject, row);
        }
    }

    // §2.4 trusted-dependency: a selected goal's grounded slice reaches a
    // user `assume`/`admit` or an `external_body` contract. Reported per
    // trusted subject with the roots it supports. This is why a vacuous goal
    // and a trusted dependency are usually two views of one situation.
    let external_body_owners: BTreeSet<&str> = records[record_index]
        .source_functions
        .iter()
        .filter(|f| f.external_body)
        .map(|f| f.fun.as_str())
        .collect();
    // id → (kind, owner) for this record's artifacts; the graph does not carry
    // these directly.
    let artifact_meta: BTreeMap<&str, (&record::ArtifactKind, &str)> = records[record_index]
        .artifacts
        .iter()
        .map(|a| (a.id.as_str(), (&a.kind, a.owner.as_str())))
        .collect();
    let mut trusted: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    for vertex in data
        .direct_support
        .iter()
        .chain(data.direct_contradiction.iter())
        .chain(data.transitive.iter())
    {
        let Some(info) = g.vertex_info.get(vertex) else { continue };
        // Only premises can be trusted material: an obligation is discharged,
        // not assumed.
        if info.role != Some(record::Role::Premise) {
            continue;
        }
        let assumed = matches!(info.emission, Some(record::EmissionRole::UserAssumption));
        let assumption_trust = if assumed {
            match assumption_source(info.span.as_deref()) {
                AssumptionSource::Explicit(kind) => Some(kind),
                AssumptionSource::OtherSourceConstruct => None,
                AssumptionSource::Unavailable => Some("user-assumption-or-admission"),
            }
        } else {
            None
        };
        // For an `external_body` callee only the *ensures* side is trusted —
        // it is assumed without a proof. Its `requires` is an obligation the
        // caller discharges, so it is not trusted material.
        let imported_trusted =
            info.artifact.as_deref().and_then(|a| artifact_meta.get(a)).is_some_and(
                |(kind, owner)| {
                    external_body_owners.contains(owner)
                        && matches!(
                            kind,
                            record::ArtifactKind::EnsuresAggregate
                                | record::ArtifactKind::EnsuresClause
                                | record::ArtifactKind::LemmaEnsuresClause
                        )
                },
            );
        if assumption_trust.is_none() && !imported_trusted {
            continue;
        }
        let subject = info.artifact.clone().unwrap_or_else(|| vertex.clone());
        trusted.entry(subject.clone()).or_insert_with(|| {
            serde_json::json!({
                "kind": "trusted-dependency",
                "claim": "trust",
                // Positive reachability: the subject is *in* the slice.
                "evidence_basis": "slice-reachability",
                "family": "trusted-dependency",
                "trust": assumption_trust.unwrap_or("external-body-contract"),
                "presentation": "traceability",
                "root_policy": root_policy,
                "subject": subject,
                // Where the trusted material is *defined*.
                "span": info.span,
                "owner": info.fun,
                // The function whose proof consumes it. One row is a
                // (consumer, subject) relation; project and file scope
                // aggregate by subject and keep this list.
                "consumer": function,
            })
        });
    }

    // §2.5 goal-without-body-support: a declared goal of an executable
    // function whose grounded slice contains no local implementation fact.
    // Structural proof coupling, not a claim the specification is weak.
    let mut weak_coupling: Vec<serde_json::Value> = Vec::new();
    if gate.open() {
        let has_local_impl = data
            .direct_support
            .iter()
            .chain(data.transitive.iter())
            .filter_map(|v| g.vertex_info.get(v))
            .any(|info| {
                info.fun.as_deref() == Some(function)
                    && info
                        .artifact
                        .as_deref()
                        .and_then(|a| artifact_meta.get(a))
                        .is_some_and(|(kind, _)| program_fact(kind))
            });
        if !has_local_impl && !data.roots.is_empty() {
            weak_coupling.push(serde_json::json!({
                "kind": "goal-without-body-support",
                "claim": "coupling",
                // Derived by absence — "no local implementation fact in the
                // slice" — even though it renders as coupling. An unlicensed
                // export can drop the very assignment that would have
                // satisfied it, so this must be withheld like any other
                // absence claim.
                "evidence_basis": "slice-absence",
                "family": "weak-proof-coupling",
                "presentation": "review",
                "root_policy": root_policy,
                "function": function,
                "roots": data.roots.iter().map(|r| r.target.clone()).collect::<Vec<_>>(),
            }));
        }
    }
    if every_root_vacuous {
        for row in weak_coupling.drain(..) {
            let key = row
                .get("function")
                .and_then(|value| value.as_str())
                .unwrap_or(function)
                .to_string();
            secondary.insert(
                format!("coupling:{key}"),
                secondary_observation(row, "all-selected-roots-vacuous"),
            );
        }
    }

    let findings: Vec<serde_json::Value> = primary_uncovered
        .into_values()
        .chain(vacuous.into_values())
        .chain(trusted.into_values())
        .chain(weak_coupling)
        .collect();

    let roots: Vec<serde_json::Value> = data
        .roots
        .iter()
        .map(|row| {
            let parent_info = row.parent.as_deref().and_then(|parent| g.vertex_info.get(parent));
            serde_json::json!({
                "target": row.target,
                "parent": row.parent,
                "artifact": parent_info
                    .and_then(|info| info.artifact.as_deref())
                    .map(&de_ns),
                "span": parent_info
                    .and_then(|info| info.span.clone())
                    .unwrap_or_else(|| row.span.clone()),
                "query_id": row.query_id,
                "coverage_eligibility": coverage_eligibility(row),
            })
        })
        .collect();

    let witnesses: Vec<serde_json::Value> = data
        .witnesses
        .iter()
        .map(|witness| {
            serde_json::json!({
                "query_id": witness.query_id,
                "root": witness.root,
                "observed": witness.observed,
                "members": witness.members,
            })
        })
        .collect();

    let steps: Vec<serde_json::Value> = data
        .steps
        .iter()
        .map(|step| {
            serde_json::json!({
                "kind": research_relation(step.kind),
                "head": step.head,
                "tail": step.tail,
                "query_id": step.query,
                "why": step.why,
            })
        })
        .collect();

    // Every ref used above resolves in this table.
    let mut refs: BTreeSet<String> = BTreeSet::new();
    for class_refs in classes.values() {
        refs.extend(class_refs.values().flatten().cloned());
    }
    refs.extend(data.generated_support.iter().cloned());
    refs.extend(data.ambient_support.iter().cloned());
    for witness in &data.witnesses {
        refs.extend(witness.members.iter().cloned());
    }
    for step in &data.steps {
        refs.insert(step.head.clone());
        refs.extend(step.tail.iter().cloned());
    }
    for row in data.roots.iter() {
        if let Some(parent) = &row.parent {
            refs.insert(parent.clone());
        }
    }
    let vertices: BTreeMap<&String, serde_json::Value> =
        refs.iter().map(|vertex| (vertex, vertex_json(vertex))).collect();

    serde_json::json!({
        "semantics": "selected roots; sets derive only from their atomic witnesses and productive grounded slices",
        "policy": policy,
        "state": if data.roots.is_empty() { "no-declared-goals" } else { "rooted" },
        "root_policy": root_policy,
        "root_reason": root_reason,
        // How a finding under this root set must be read.
        "finding_relation": relation,
        "weak_coupling_eligible": gate.open(),
        "completeness": rooted_completeness,
        "roots": roots,
        "classification": classification,
        "generated_support": data.generated_support,
        "ambient_support": data.ambient_support,
        "witnesses": witnesses,
        "steps": steps,
        "boundaries": data.boundaries.iter().map(boundary_json).collect::<Vec<_>>(),
        "findings": findings,
        // Evidence intentionally not promoted to a developer finding. Kept
        // here so a study can inspect how often vacuity or root intent
        // dominated a lower-level observation without inflating finding
        // counts.
        "secondary_observations": secondary.into_values().collect::<Vec<_>>(),
        // Non-root vacuity of extent `some`. Collapsed by default: a dead
        // branch is information, not a defect.
        "infeasible_paths": {
            "count": infeasible.len(),
            "collapsed": true,
            "rows": infeasible.values().cloned().collect::<Vec<_>>(),
        },
        "vertices": vertices,
    })
}

fn research_text(g: &Graph, records: &[CoverageRecord], filter: &str, policy: CallPolicy) {
    let all_targets = targets(records);
    let exact_target = all_targets.iter().any(|row| row.target == filter);
    let mut matched: Vec<&TargetRow> = all_targets
        .iter()
        .filter(|row| {
            filter.is_empty()
                || row.target == filter
                || row.fun.contains(filter)
                || row.parent.as_deref().unwrap_or("").contains(filter)
        })
        .collect();
    if !exact_target {
        matched.retain(|row| {
            row.parent.as_ref().is_some_and(|parent| g.spec_obligations.contains(parent))
        });
    }

    let options = SliceOptions { calls: policy };
    let mut slices = g.backward_slices(
        matched
            .iter()
            .filter(|row| !not_applicable(row) && (!row.evidence_measured || row.target_observed))
            .map(|row| row.target.clone()),
        options,
    );
    let findings = projection::project(records);
    let mut by_function: BTreeMap<(usize, String), Vec<(&TargetRow, Option<Slice>)>> =
        BTreeMap::new();

    println!("proof-coverage-text 0.1");
    println!("calls={}", if policy == CallPolicy::Opaque { "opaque" } else { "modular" });

    for row in matched {
        let parent =
            row.parent.as_deref().map(|parent| g.display_friendly(parent)).unwrap_or_default();
        println!();
        println!("query {}", row.target);
        if records.len() > 1 {
            println!("record {}", row.record_index);
        }
        println!("function {}", g.display_function(&row.fun));
        println!("terminal {}", if parent.is_empty() { "-" } else { parent.as_str() });
        println!(
            "measurement={} target={}",
            if not_applicable(row) {
                "not-applicable"
            } else if row.evidence_measured {
                "measured"
            } else {
                "unmeasured"
            },
            if row.target_observed { "observed" } else { "not-observed" },
        );

        if not_applicable(row) {
            by_function.entry((row.record_index, row.fun.clone())).or_default().push((row, None));
            continue;
        }

        let direct = focused_evidence(records, row);
        if let Some(witness) = &direct {
            println!(
                "{} query={}",
                if row.target_observed { "support-witness" } else { "contradiction-witness" },
                row.query_id,
            );
            for class in ["source", "generated", "ambient", "background"] {
                let vertices: BTreeSet<String> = witness
                    .iter()
                    .filter(|vertex| research_vertex_class(g, vertex) == class)
                    .cloned()
                    .collect();
                print_research_set(class, &vertices, g);
            }
        } else {
            println!("witness none");
        }

        let slice = if row.evidence_measured && !row.target_observed {
            Slice {
                target: row.target.clone(),
                definite: BTreeSet::new(),
                possible: BTreeSet::new(),
                boundaries: Vec::new(),
                steps: Vec::new(),
            }
        } else {
            slices.remove(&row.target).expect("research slicer omitted requested target")
        };
        let direct = direct.unwrap_or_default();
        let imported: BTreeSet<String> = slice
            .boundaries
            .iter()
            .filter_map(|boundary| match boundary {
                Boundary::Call { premise, .. } => Some(premise.clone()),
                _ => None,
            })
            .collect();
        let source_nodes: BTreeSet<String> = direct
            .iter()
            .chain(slice.definite.iter())
            .filter(|vertex| {
                g.vertex_info.get(*vertex).and_then(|info| info.artifact.as_ref()).is_some()
            })
            .cloned()
            .collect();
        for vertex in source_nodes {
            println!(
                "node reach={} locality={} value={}",
                if direct.contains(&vertex) { "direct" } else { "transitive" },
                if imported.contains(&vertex) { "imported" } else { "local" },
                g.display_friendly(&vertex),
            );
        }

        for (index, step) in slice.steps.iter().enumerate() {
            println!(
                "edge E{} kind={} query={}",
                index + 1,
                research_relation(step.kind),
                step.query.map(|query| query.to_string()).unwrap_or("-".into()),
            );
            let display_tail: BTreeSet<String> = if step.kind == analysis::ArcKind::SupportedBy {
                step.tail
                    .iter()
                    .filter(|vertex| research_vertex_class(g, vertex) != "background")
                    .cloned()
                    .collect()
            } else {
                step.tail.clone()
            };
            print_research_set("tail", &display_tail, g);
            println!("  head={{{}}}", g.display_friendly(&step.head));
        }

        for boundary in &slice.boundaries {
            println!("boundary {}", boundary_json(boundary));
        }
        for vertex in &slice.definite {
            if g.vertex_info.get(vertex).is_some_and(|info| info.unresolved) {
                println!("gap kind=attribution-unresolved node={}", g.display_friendly(vertex));
            }
        }
        for vertex in &slice.possible {
            println!("gap kind=unmeasured-scope node={}", g.display_friendly(vertex));
        }
        print_query_findings(g, &findings.queries, &row.target);
        by_function
            .entry((row.record_index, row.fun.clone()))
            .or_default()
            .push((row, Some(slice)));
    }

    for ((record_index, function), rows) in by_function {
        let data = rooted_data(g, records, &all_targets, record_index, &function, &rows);
        let roots: BTreeSet<String> = data.roots.iter().map(|row| row.target.clone()).collect();
        let mut aux_support: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (artifact, aux) in &data.aux_rows {
            for row in aux {
                let terminal = row
                    .parent
                    .as_deref()
                    .map(|parent| g.display_friendly(parent))
                    .unwrap_or_else(|| row.target.clone());
                aux_support
                    .entry(artifact.clone())
                    .or_default()
                    .push(format!("terminal={} query={}", terminal, row.query_id));
            }
        }

        println!();
        if records.len() > 1 {
            println!("record {}", record_index);
        }
        println!("function {}", g.display_function(&function));
        if let Some(sf) = source_function(records, record_index, &function) {
            println!("  {}", source_function_text(sf));
        }
        print_research_set("roots", &roots, g);
        print_research_set("direct-support", &data.direct_support, g);
        print_research_set("direct-contradiction", &data.direct_contradiction, g);
        print_research_set("transitive", &data.transitive, g);
        print_research_set("generated-support", &data.generated_support, g);
        print_research_set("ambient-support", &data.ambient_support, g);
        for boundary in &data.boundaries {
            println!("boundary {}", boundary_json(boundary));
        }
        // Denominator framing: query-scope observations are the raw
        // material; only root-scoped survivors below are findings.
        let observation_count = findings
            .queries
            .iter()
            .filter(|finding| match finding {
                QueryFinding::UncoveredPremise { terminal, .. } => {
                    terminal.record_index == record_index && terminal.function == function
                }
                _ => false,
            })
            .count();
        if observation_count > 0 {
            println!(
                "observations available-not-observed={} across this function's queries \
                 (findings below are the root-scoped survivors)",
                observation_count
            );
        }
        print_function_findings(
            g,
            &findings.queries,
            &roots,
            &data.covered_artifacts,
            &aux_support,
            record_index,
            &function,
            &study_gate(records, record_index, &function, &roots),
        );
    }
}

/// Forward direction: what depends on a fact.
///
/// Two relations, both witness-relative and both named as such. `reaches` is
/// may-depend: every vertex whose observed argument mentions the target
/// somewhere in a productive tail (plain reachability). `load-bearing` is the
/// stronger statement: the obligations that lose their grounding in the
/// observed argument when the target is blocked. Neither claims the proof
/// would fail without the fact; cores are non-minimal and a deletion
/// candidate needs re-verification.
fn impact_text(g: &Graph, records: &[CoverageRecord], target: &str, policy: CallPolicy) {
    let options = SliceOptions { calls: policy };
    let multi = records.len() > 1;
    // Accept an artifact id, a namespaced vertex, or (single record) a label.
    let resolved = if g.vertex_info.contains_key(target) || g.artifact_ids.contains(target) {
        target.to_string()
    } else if !multi {
        target.to_string()
    } else {
        eprintln!("impact: unknown target {target}");
        std::process::exit(2);
    };
    let seed = g.forward_seed(&resolved);
    println!("proof-coverage-text 0.1");
    println!(
        "impact target={} calls={}",
        resolved,
        match policy {
            CallPolicy::Opaque => "opaque",
            CallPolicy::Modular => "modular",
        }
    );
    print_research_set("seed", &seed, g);
    let reached = g.forward_reach(&seed, options);
    let reached_obligations: BTreeSet<String> =
        reached.iter().filter(|v| g.obligations.contains(*v)).cloned().collect();
    let reached_premises: BTreeSet<String> = reached
        .iter()
        .filter(|v| !g.obligations.contains(*v) && !seed.contains(*v))
        .cloned()
        .collect();
    print_research_set(
        "reaches-obligations (may-depend, witness-relative)",
        &reached_obligations,
        g,
    );
    print_research_set("reaches-premises (through certificates)", &reached_premises, g);
    let mut load_bearing: BTreeSet<String> = BTreeSet::new();
    for vertex in &seed {
        load_bearing.extend(g.ablate(vertex));
    }
    print_research_set(
        "load-bearing (blocked => ungrounded in the observed argument; not a deletion claim)",
        &load_bearing,
        g,
    );
    // Functions whose obligations are reached, for the system-level reading.
    let mut functions: BTreeSet<String> = BTreeSet::new();
    for v in &reached_obligations {
        if let Some(f) = g.vertex_info.get(v).and_then(|i| i.fun.clone()) {
            functions.insert(f);
        }
    }
    println!("reaches-functions={{");
    for f in functions {
        println!("    {}", g.display_function(&f));
    }
    println!("}}");
}

/// `path:l:c: l:c (#n)` → (path, first line, last line). Verus spans are
/// absolute or relative to the invocation directory; both are opened as given.
fn span_location(span: &str) -> Option<(String, usize, usize)> {
    let cut = span.rfind(".rs:")? + 4;
    let path = span[..cut - 1].to_string();
    let rest = &span[cut..];
    let mut nums = rest
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .filter_map(|s| s.parse::<usize>().ok());
    let start = nums.next()?;
    nums.next();
    let end = nums.next().unwrap_or(start);
    Some((path, start, end.max(start)))
}

/// One inspectable findings report over the whole record set: grouped by file
/// and function, each row quoting the source it names so a reader — human or
/// agent — does not have to open the files to judge it.
///
/// Withheld rows are shown but marked: they are the rows whose slice rests on
/// an unlicensed exported assumption, and the point of showing them is that
/// they are the ones *not* to act on.
fn print_findings_report(report: &serde_json::Value, show_all: bool) {
    let mut sources: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut quote = |span: Option<&str>| -> Vec<String> {
        let Some((path, start, end)) = span.and_then(span_location) else { return vec![] };
        let lines = sources.entry(path.clone()).or_insert_with(|| {
            std::fs::read_to_string(&path)
                .map(|text| text.lines().map(str::to_string).collect())
                .unwrap_or_default()
        });
        if lines.is_empty() {
            return vec![];
        }
        // Long regions (a whole loop, an assert-forall body) would swamp the
        // report; quote the head and say how much was elided.
        let last = end.min(start + 2).min(lines.len());
        let mut out: Vec<String> = (start..=last)
            .filter_map(|n| lines.get(n - 1).map(|text| format!("  {n:>5} | {text}")))
            .collect();
        if end > last {
            out.push(format!("        | ... {} more lines", end - last));
        }
        out
    };

    let severity = |kind: &str, defensible: bool| -> u8 {
        if !defensible {
            return 4;
        }
        match kind {
            k if k.starts_with("vacuous-") => 0,
            "trusted-dependency" => 3,
            "goal-without-body-support" => 2,
            _ => 1,
        }
    };

    // Absolute spans make the report unreadable and machine-specific; show
    // them relative to the invocation directory when possible.
    let cwd = std::env::current_dir().ok().map(|p| format!("{}/", p.display()));
    let trim = |s: &str| -> String {
        match &cwd {
            Some(prefix) => s.replace(prefix.as_str(), ""),
            None => s.to_string(),
        }
    };

    println!("proof-coverage-findings 0.2");
    println!(
        "schema={} policy={} records={}",
        report.get("schema").and_then(|v| v.as_str()).unwrap_or("?"),
        report.get("call_policy").and_then(|v| v.as_str()).unwrap_or("?"),
        report.get("record_count").and_then(|v| v.as_u64()).unwrap_or(0),
    );
    println!();

    let functions = report.get("functions").and_then(|v| v.as_array()).cloned().unwrap_or_default();
    let mut by_file: BTreeMap<String, Vec<&serde_json::Value>> = BTreeMap::new();
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    let mut total = 0usize;
    let mut withheld = 0usize;
    let mut trust_relations = 0usize;
    let mut trusted_subjects = BTreeSet::new();
    let mut secondary_total = 0usize;
    let mut functions_with_findings = 0usize;
    for function in &functions {
        let rows = function.get("findings").and_then(|v| v.as_array());
        let secondary = function.get("secondary_observations").and_then(|v| v.as_array());
        if rows.is_none_or(|rows| rows.is_empty()) && secondary.is_none_or(|rows| rows.is_empty()) {
            continue;
        }
        if rows.is_some_and(|rows| !rows.is_empty()) {
            functions_with_findings += 1;
        }
        for row in rows.into_iter().flatten() {
            total += 1;
            *kinds
                .entry(row.get("kind").and_then(|v| v.as_str()).unwrap_or("?").to_string())
                .or_default() += 1;
            if row.get("defensible").and_then(|v| v.as_bool()) == Some(false) {
                withheld += 1;
            }
            if row.get("claim").and_then(|v| v.as_str()) == Some("trust") {
                trust_relations += 1;
                if let Some(subject) = row.get("subject").and_then(|v| v.as_str()) {
                    trusted_subjects.insert(subject.to_string());
                }
            }
        }
        secondary_total += secondary.map(Vec::len).unwrap_or(0);
        let file = function
            .get("source")
            .and_then(|s| s.get("span"))
            .and_then(|s| s.as_str())
            .and_then(|s| s.rfind(".rs:").map(|end| s[..end + 3].to_string()))
            .unwrap_or_else(|| "(unknown file)".to_string());
        by_file.entry(file).or_default().push(function);
    }

    println!("SUMMARY");
    println!("  functions with findings: {functions_with_findings}");
    println!("  findings: {total} ({} defensible, {withheld} withheld)", total - withheld);
    println!(
        "  review findings: {}",
        total.saturating_sub(trust_relations).saturating_sub(withheld)
    );
    println!(
        "  trusted-dependency relations: {trust_relations} ({} distinct subject(s))",
        trusted_subjects.len()
    );
    println!("  secondary observations: {secondary_total}");
    for (kind, n) in &kinds {
        println!("    {n:>5}  {kind}");
    }
    if withheld > 0 {
        println!();
        println!("  {withheld} withheld: root evidence is incomplete or source attribution is");
        println!("  occluded, so a supporting fact may have dropped out. Do not act on these.");
    }
    println!();

    for (file, mut rows) in by_file {
        println!("═══ {}", trim(&file));
        rows.sort_by_key(|f| f.get("function").and_then(|v| v.as_str()).unwrap_or("").to_string());
        for function in rows {
            let name = function.get("function").and_then(|v| v.as_str()).unwrap_or("?");
            let licensing = function
                .get("completeness")
                .and_then(|c| c.get("licensing"))
                .and_then(|l| l.get("status"))
                .and_then(|s| s.as_str())
                .unwrap_or("?");
            println!();
            println!("── {name}");
            println!(
                "   status={} roots={} licensing={}",
                function.get("status").and_then(|v| v.as_str()).unwrap_or("?"),
                function.get("root_policy").and_then(|v| v.as_str()).unwrap_or("?"),
                licensing,
            );
            if let Some(reason) = function.get("root_reason").and_then(|v| v.as_str()) {
                println!("   root_reason={reason}");
            }
            let mut findings: Vec<&serde_json::Value> = function
                .get("findings")
                .and_then(|v| v.as_array())
                .map(|v| v.iter().collect())
                .unwrap_or_default();
            findings.sort_by_key(|row| {
                let kind = row.get("kind").and_then(|v| v.as_str()).unwrap_or("");
                let ok = row.get("defensible").and_then(|v| v.as_bool()).unwrap_or(true);
                (severity(kind, ok), kind.to_string())
            });
            // Trusted dependencies are numerous and informational; collapse
            // them unless asked for. They are a property of the proof, not a
            // defect (§2.4).
            let (trust, rest): (Vec<_>, Vec<_>) = findings
                .into_iter()
                .partition(|row| row.get("claim").and_then(|v| v.as_str()) == Some("trust"));
            for row in rest {
                let kind = row.get("kind").and_then(|v| v.as_str()).unwrap_or("?");
                let defensible = row.get("defensible").and_then(|v| v.as_bool()).unwrap_or(true);
                let span = row
                    .get("source")
                    .and_then(|s| s.get("span"))
                    .or_else(|| row.get("span"))
                    .and_then(|s| s.as_str());
                println!();
                println!("   [{}] {kind}", if defensible { "  " } else { "WH" });
                if let Some(subject) =
                    row.get("source").and_then(|s| s.get("artifact")).and_then(|v| v.as_str())
                {
                    println!("       subject  {subject}");
                }
                if let Some(span) = span {
                    println!("       at       {}", trim(span));
                }
                let quoted = quote(span);
                let explicit_contradiction = quoted.iter().any(|line| {
                    line.contains("assert(false)")
                        || line.split_once('|').is_some_and(|(_, source)| {
                            source.trim().trim_end_matches(',') == "false"
                        })
                });
                for line in &quoted {
                    println!("     {line}");
                }
                // Whole-function findings name no source subject; say what they
                // mean rather than printing a bare kind.
                if kind == "goal-without-body-support" {
                    let roots =
                        row.get("roots").and_then(|v| v.as_array()).map(|v| v.len()).unwrap_or(0);
                    println!(
                        "       in       {}",
                        row.get("function").and_then(|v| v.as_str()).unwrap_or(name)
                    );
                    println!(
                        "       means    none of this function's {roots} declared goal(s) \
                         reached a local implementation fact"
                    );
                    println!(
                        "                the contract may be weakly coupled to the body; it is \
                         not a claim the spec is wrong"
                    );
                }
                if let Some(extent) = row.get("extent").and_then(|v| v.as_str()) {
                    println!(
                        "       extent   {extent} ({} of {} terminals vacuous){}",
                        row.get("vacuous_terminals").and_then(|v| v.as_u64()).unwrap_or(0),
                        row.get("obligation_terminals").and_then(|v| v.as_u64()).unwrap_or(0),
                        if explicit_contradiction {
                            " — explicit contradiction goal; often intentional"
                        } else if extent == "all" {
                            " — discharged entirely by contradictory context"
                        } else {
                            " — the others are proved; these are dead paths"
                        },
                    );
                }
                if let Some(relation) = row.get("root_relation").and_then(|v| v.as_str()) {
                    println!("       roots    {relation}");
                }
                if let Some(relation) = row.get("finding_relation").and_then(|v| v.as_str()) {
                    println!("       means    {relation}");
                }
                if let Some(verdict) = row.get("verdict").and_then(|v| v.as_str()) {
                    println!("       verdict  {verdict}");
                }
                let aux = row.get("auxiliary_support").and_then(|v| v.as_array());
                if let Some(aux) = aux.filter(|a| !a.is_empty()) {
                    println!(
                        "       observed by {} non-root obligation(s), so it is not dead",
                        aux.len()
                    );
                }
                if !defensible {
                    println!(
                        "       WITHHELD {}",
                        row.get("withheld_reason").and_then(|v| v.as_str()).unwrap_or("?")
                    );
                }
            }
            if !trust.is_empty() {
                println!();
                if show_all {
                    for row in &trust {
                        println!(
                            "   [  ] trusted-dependency  {} ({})",
                            row.get("subject").and_then(|v| v.as_str()).unwrap_or("?"),
                            row.get("trust").and_then(|v| v.as_str()).unwrap_or("?"),
                        );
                    }
                } else {
                    let mut by_trust: BTreeMap<&str, Vec<&&serde_json::Value>> = BTreeMap::new();
                    for row in &trust {
                        by_trust
                            .entry(row.get("trust").and_then(|v| v.as_str()).unwrap_or("?"))
                            .or_default()
                            .push(row);
                    }
                    for (trust_kind, rows) in by_trust {
                        let subjects: BTreeSet<&str> = rows
                            .iter()
                            .filter_map(|row| row.get("subject").and_then(|v| v.as_str()))
                            .collect();
                        println!(
                            "   [i ] trusted-dependency {trust_kind} × {} — {} distinct \
                             subject(s); --all to list",
                            rows.len(),
                            subjects.len(),
                        );
                    }
                }
            }
            let secondary = function.get("secondary_observations").and_then(|v| v.as_array());
            if let Some(secondary) = secondary.filter(|rows| !rows.is_empty()) {
                println!();
                if show_all {
                    for row in secondary {
                        let kind = row.get("kind").and_then(|v| v.as_str()).unwrap_or("?");
                        let reason =
                            row.get("secondary_reason").and_then(|v| v.as_str()).unwrap_or("?");
                        println!("   [i ] {kind} — secondary: {reason}");
                        if let Some(subject) = row
                            .get("source")
                            .and_then(|source| source.get("artifact"))
                            .and_then(|value| value.as_str())
                        {
                            println!("       subject  {subject}");
                        }
                    }
                } else {
                    let mut reasons: BTreeMap<&str, usize> = BTreeMap::new();
                    for row in secondary {
                        *reasons
                            .entry(
                                row.get("secondary_reason").and_then(|v| v.as_str()).unwrap_or("?"),
                            )
                            .or_default() += 1;
                    }
                    for (reason, count) in reasons {
                        println!(
                            "   [i ] secondary-observation × {count} — {reason}; --all to list"
                        );
                    }
                }
            }
            let infeasible = function
                .get("rooted")
                .and_then(|r| r.get("infeasible_paths"))
                .and_then(|i| i.get("count"))
                .and_then(|v| v.as_u64())
                .unwrap_or(0);
            if infeasible > 0 {
                println!();
                println!("   [  ] infeasible-path × {infeasible} (dead branches, collapsed)");
            }
        }
        println!();
    }

    if total == 0 {
        println!("no findings");
    }
}

fn report_json(g: &Graph, records: &[CoverageRecord], policy: CallPolicy) -> serde_json::Value {
    let options = SliceOptions { calls: policy };
    let target_rows = targets(records);
    // Computed once for the whole graph; the licensing dimension of every
    // query and function slice is an intersection against this set.
    let fail_open = fail_open_roots(g);
    let finding_projection = projection::project(records);
    let mut function_findings: BTreeMap<(usize, String), ScopeProjection> = finding_projection
        .functions
        .iter()
        .map(|projection| {
            (
                (projection.record_index, projection.function.clone()),
                ScopeProjection {
                    premise_coverage: projection.premise_coverage.clone(),
                    findings: projection.findings.clone(),
                },
            )
        })
        .collect();
    let mut slices_by_target = g.backward_slices(
        target_rows.iter().filter(|row| !not_applicable(row)).map(|row| row.target.clone()),
        options,
    );
    let mut query_rows = Vec::new();
    let mut by_function: BTreeMap<(usize, String), Vec<(&TargetRow, Option<Slice>)>> =
        BTreeMap::new();

    for row in &target_rows {
        let is_postcondition =
            row.parent.as_ref().is_some_and(|parent| g.spec_obligations.contains(parent));
        if not_applicable(row) {
            query_rows.push(serde_json::json!({
                "target": row.target,
                "record_index": row.record_index,
                "parent": row.parent,
                "function": row.fun,
                "description": row.desc,
                "span": row.span,
                "terminal_path": row.terminal_path,
                "kind": if is_postcondition { "postcondition" } else { "obligation" },
                "status": "NotApplicable",
                "completeness": not_applicable_completeness(),
                "shadow_result": row.shadow_result,
                "coverage_eligibility": coverage_eligibility(row),
                "definite": [],
                "possible": [],
                "definite_artifacts": [],
                "possible_artifacts": [],
                "boundaries": [],
            }));
            by_function.entry((row.record_index, row.fun.clone())).or_default().push((row, None));
            continue;
        }
        let slice =
            slices_by_target.remove(&row.target).expect("batch slicer omitted requested target");
        let status = slice_status(g, &slice, &fail_open);
        query_rows.push(serde_json::json!({
            "target": row.target,
            "record_index": row.record_index,
            "parent": row.parent,
            "function": row.fun,
            "description": row.desc,
            "span": row.span,
            "terminal_path": row.terminal_path,
            "kind": if is_postcondition { "postcondition" } else { "obligation" },
            "status": status,
            "completeness": completeness_json(g, &slice, &fail_open),
            "shadow_result": row.shadow_result,
            "coverage_eligibility": coverage_eligibility(row),
            "definite": slice.definite,
            "possible": slice.possible,
            "definite_artifacts": projected_artifacts(g, &slice.definite),
            "possible_artifacts": projected_artifacts(g, &slice.possible),
            "boundaries": slice.boundaries.iter().map(boundary_json).collect::<Vec<_>>(),
        }));
        by_function
            .entry((row.record_index, row.fun.clone()))
            .or_default()
            .push((row, Some(slice)));
    }

    let mut function_rows = Vec::new();
    for ((record_index, fun), slices) in by_function {
        let mut definite = BTreeSet::new();
        let mut possible = BTreeSet::new();
        let mut boundaries = BTreeSet::new();
        let mut steps = BTreeSet::new();
        let mut terminals = Vec::new();
        let mut postcondition_terminals = Vec::new();
        let mut terminal_statuses: BTreeMap<&'static str, usize> = BTreeMap::new();
        let mut coverage_terminal_counts: BTreeMap<&'static str, usize> = BTreeMap::new();
        for (row, slice) in &slices {
            let terminal_status = slice
                .as_ref()
                .map(|slice| slice_status(g, slice, &fail_open))
                .unwrap_or("NotApplicable");
            *terminal_statuses.entry(terminal_status).or_default() += 1;
            *coverage_terminal_counts.entry(coverage_eligibility(row)).or_default() += 1;
            terminals.push(row.target.clone());
            if row.parent.as_ref().is_some_and(|parent| g.spec_obligations.contains(parent)) {
                postcondition_terminals.push(row.target.clone());
            }
            if let Some(slice) = slice {
                definite.extend(slice.definite.iter().cloned());
                possible.extend(slice.possible.iter().cloned());
                boundaries.extend(slice.boundaries.iter().cloned());
                steps.extend(slice.steps.iter().cloned());
            }
        }
        // Root-scoped results: postcondition terminals are the default
        // roots. A vacuous root contributes its contradiction witness but
        // no slice (mirrors the study view); not-applicable roots
        // contribute nothing.
        //
        // A function with no declared goals (no postcondition terminal —
        // typically a `proof fn` whose purpose is its own assertions) falls
        // back to `all-measured`: its measured terminals become the roots.
        // Without this, the root set is empty, every candidate is trivially
        // "outside every root slice", and the survivor rule of
        // `PROOF_COVERAGE_FINDINGS.md` §1 does no filtering at all. The
        // fallback is recorded on the function so a reader knows which
        // obligations a finding is relative to; a finding under it means
        // "unused by all measured obligations", not "unused by declared
        // goals". If there are no measured terminals either, no roots are
        // selected and no findings are emitted — only the function state.
        let has_declared_goals = slices.iter().any(|(row, _)| {
            row.parent.as_ref().is_some_and(|parent| g.spec_obligations.contains(parent))
        });
        let (root_policy, root_reason) = if has_declared_goals {
            ("declared-goals", None)
        } else if slices.iter().any(|(row, _)| row.evidence_measured) {
            ("all-measured", Some("no-declared-goals-fallback"))
        } else {
            ("none", Some("no-measured-terminals"))
        };
        let relation: &'static str = match root_policy {
            "declared-goals" => "unused by declared goals",
            "all-measured" => "unused by all measured obligations",
            _ => "no roots selected; no findings emitted",
        };
        // §2.5 weak-coupling gate, from snapshot-1 metadata. Absent metadata
        // closes the gate: a function we cannot classify gets no weak-coupling
        // finding.
        let sf = source_function(records, record_index, &fun);
        let gate = WeakCouplingGate {
            executable: sf.is_some_and(|f| f.mode == record::FunctionMode::Exec),
            has_body: sf.is_some_and(|f| f.has_body),
            body_visible: sf.is_some_and(|f| {
                matches!(f.body_visibility, record::BodyVisibility::Visible { .. })
            }),
            external_body: sf.is_none_or(|f| f.external_body),
            has_declared_goals,
        };
        let rooted_rows: Vec<(&TargetRow, Option<Slice>)> = slices
            .iter()
            .filter(|(row, _)| match root_policy {
                "declared-goals" => {
                    row.parent.as_ref().is_some_and(|parent| g.spec_obligations.contains(parent))
                }
                "all-measured" => row.evidence_measured,
                _ => false,
            })
            .map(|(row, slice)| {
                if not_applicable(row) {
                    (*row, None)
                } else if row.evidence_measured && !row.target_observed {
                    (
                        *row,
                        Some(Slice {
                            target: row.target.clone(),
                            definite: BTreeSet::new(),
                            possible: BTreeSet::new(),
                            // Preserve the fact that this selected root has no
                            // grounded proof slice. Dropping this boundary made
                            // rooted completeness contradict the function
                            // status (`Ungrounded` versus `Grounded`).
                            boundaries: vec![Boundary::Ungrounded { vertex: row.target.clone() }],
                            steps: Vec::new(),
                        }),
                    )
                } else {
                    (*row, slice.clone())
                }
            })
            .collect();
        let rooted = rooted_data(g, records, &target_rows, record_index, &fun, &rooted_rows);
        // Completeness over the *selected roots* only. Findings are scoped to
        // the roots, so their defensibility must be too: a licensing hole in
        // an unrelated auxiliary query of the same function does not affect
        // what a root's slice measured, and withholding root findings for it
        // loses valid results. The function-wide `completeness` below is kept
        // as the function's own status.
        let rooted_aggregate = Slice {
            target: fun.clone(),
            definite: rooted_rows
                .iter()
                .filter_map(|(_, slice)| slice.as_ref())
                .flat_map(|slice| slice.definite.iter().cloned())
                .collect(),
            possible: rooted_rows
                .iter()
                .filter_map(|(_, slice)| slice.as_ref())
                .flat_map(|slice| slice.possible.iter().cloned())
                .collect(),
            boundaries: rooted_rows
                .iter()
                .filter_map(|(_, slice)| slice.as_ref())
                .flat_map(|slice| slice.boundaries.iter().cloned())
                .collect(),
            steps: Vec::new(),
        };
        let rooted_completeness = if rooted_rows.is_empty() {
            not_applicable_completeness()
        } else {
            completeness_json(g, &rooted_aggregate, &fail_open)
        };
        let occluded_details: BTreeSet<String> = records[record_index]
            .queries
            .iter()
            .filter(|query| query.fun == fun)
            .flat_map(|query| query.occurrences.iter())
            .filter(|occurrence| {
                occurrence.origin.kind == OriginKind::Source && occurrence.artifact.is_none()
            })
            .map(|occurrence| occurrence.origin.detail.clone())
            .collect();
        let rooted_value = rooted_json(
            g,
            records,
            &rooted,
            &finding_projection.queries,
            record_index,
            &fun,
            records.len(),
            match policy {
                CallPolicy::Opaque => "opaque",
                CallPolicy::Modular => "modular",
            },
            root_policy,
            root_reason,
            relation,
            &gate,
            &rooted_completeness,
            &occluded_details,
        );
        possible.retain(|vertex| !definite.contains(vertex));
        let aggregate = Slice {
            target: fun.clone(),
            definite,
            possible,
            boundaries: boundaries.into_iter().collect(),
            steps: steps.into_iter().collect(),
        };
        let status = function_status(&terminal_statuses);
        let completeness = if status == "NotApplicable" {
            not_applicable_completeness()
        } else {
            completeness_json(g, &aggregate, &fail_open)
        };
        let findings = function_findings.remove(&(record_index, fun.clone())).unwrap_or_default();
        // `PROOF_COVERAGE_FINDINGS.md` §1 and `PROOF_COVERAGE.md` §7: a
        // function-level finding is a root-scoped survivor. `premise_coverage`
        // stays as coverage *data* (§2.2 keeps `observed-some` as data, not a
        // finding), but the finding array is the root-scoped one, taken from
        // the same builder the study text uses so the two cannot drift. The
        // projection's `ObservedNone` aggregate is not root-filtered and is no
        // longer published as a finding.
        // §5/§4.2a: a finding whose slice rests on an unlicensed exported
        // assumption cannot be defended, so every row carries the verdict.
        // `defensible: false` means the supporting facts may have dropped out
        // of the slice for want of a licensing rule, not because they are
        // unused.
        //
        // Only *absence* claims are affected. A vacuous goal is measured
        // straight from the core (was the terminal in its own witness?), and a
        // trusted dependency is a positive reachability statement; neither is
        // derived by subtracting a slice, so no licensing hole can invent one.
        // Root-scoped, not function-wide: see `rooted_completeness`.
        let absence_complete = absence_evidence_complete(&rooted_completeness);
        let rooted_findings = rooted_value
            .get("findings")
            .and_then(|f| f.as_array())
            .map(|rows| {
                rows.iter()
                    .map(|row| {
                        let mut row = row.clone();
                        // Keyed on how the row was derived, not on how it
                        // renders. Anything derived by subtracting a slice can
                        // be invalidated by an unlicensed exported assumption;
                        // reachability and core-read rows cannot.
                        let positive_claim = row
                            .get("evidence_basis")
                            .and_then(|c| c.as_str())
                            .is_none_or(|c| c != "slice-absence");
                        let occluded =
                            row.get("verdict").and_then(|v| v.as_str()) == Some("occluded");
                        if let Some(obj) = row.as_object_mut() {
                            obj.insert(
                                "defensible".into(),
                                serde_json::json!(
                                    positive_claim || (absence_complete && !occluded)
                                ),
                            );
                            if !positive_claim && (!absence_complete || occluded) {
                                obj.insert(
                                    "withheld_reason".into(),
                                    serde_json::json!(if occluded {
                                        "source-attribution-occluded"
                                    } else {
                                        "incomplete-root-evidence"
                                    }),
                                );
                            }
                        }
                        row
                    })
                    .collect::<Vec<_>>()
            })
            .map(serde_json::Value::from)
            .unwrap_or_else(|| serde_json::json!([]));
        function_rows.push(serde_json::json!({
            "record_index": record_index,
            "function": fun,
            "source": source_function(records, record_index, &fun).map(source_function_json),
            "status": status,
            "completeness": completeness,
            "terminal_statuses": terminal_statuses,
            "coverage_terminal_counts": coverage_terminal_counts,
            "terminals": terminals,
            "postcondition_terminals": postcondition_terminals,
            "definite": aggregate.definite,
            "possible": aggregate.possible,
            "definite_artifacts": projected_artifacts(g, &aggregate.definite),
            "possible_artifacts": projected_artifacts(g, &aggregate.possible),
            "boundaries": aggregate.boundaries.iter().map(boundary_json).collect::<Vec<_>>(),
            "root_policy": root_policy,
            "root_reason": root_reason,
            "has_declared_goals": has_declared_goals,
            "premise_coverage": findings.premise_coverage,
            "findings": rooted_findings,
            "secondary_observations": rooted_value
                .get("secondary_observations")
                .cloned()
                .unwrap_or_else(|| serde_json::json!([])),
            "rooted": rooted_value,
        }));
    }

    // File scope aggregates the root-scoped function findings rather than
    // recombining already-aggregated coverage states, so a file's findings are
    // the same rows its functions report. `premise_coverage` stays as the
    // file's coverage data (§2.2 keeps `observed-some` as data).
    let mut findings_by_file: BTreeMap<String, Vec<serde_json::Value>> = BTreeMap::new();
    // Trusted subjects are aggregated across functions: one subject reached by
    // N proofs is one subject, not N findings. The (consumer, subject) relation
    // is kept on the function rows and listed here, so nothing is lost.
    // subject -> (row, consumers, root policies)
    let mut trusted_by_file: BTreeMap<
        String,
        BTreeMap<String, (serde_json::Value, BTreeSet<String>, BTreeSet<String>)>,
    > = BTreeMap::new();
    for row in &function_rows {
        let owner = row.get("function").and_then(|f| f.as_str()).unwrap_or_default().to_string();
        for finding in row.get("findings").and_then(|f| f.as_array()).into_iter().flatten() {
            let span = finding
                .get("source")
                .and_then(|s| s.get("span"))
                .or_else(|| finding.get("span"))
                .and_then(|s| s.as_str());
            let Some(file) = span.and_then(|s| s.rfind(".rs:").map(|end| s[..end + 3].to_string()))
            else {
                continue;
            };
            if finding.get("claim").and_then(|c| c.as_str()) == Some("trust") {
                let subject =
                    finding.get("subject").and_then(|s| s.as_str()).unwrap_or_default().to_string();
                let entry = trusted_by_file
                    .entry(file)
                    .or_default()
                    .entry(subject)
                    .or_insert_with(|| (finding.clone(), BTreeSet::new(), BTreeSet::new()));
                if let Some(consumer) =
                    finding.get("consumer").and_then(|c| c.as_str()).or(Some(owner.as_str()))
                {
                    entry.1.insert(consumer.to_string());
                }
                if let Some(policy) = finding.get("root_policy").and_then(|p| p.as_str()) {
                    entry.2.insert(policy.to_string());
                }
                continue;
            }
            // Non-trust rows keep the consuming function, which the previous
            // clone-by-span dropped: a finding's span names where the subject
            // is written, not whose proof failed to use it.
            let mut finding = finding.clone();
            if let Some(obj) = finding.as_object_mut() {
                obj.entry("function").or_insert(serde_json::json!(owner));
            }
            findings_by_file.entry(file).or_default().push(finding);
        }
    }
    for (file, subjects) in trusted_by_file {
        let rows = findings_by_file.entry(file).or_default();
        for (subject, (template, consumers, policies)) in subjects {
            let mut row = template;
            if let Some(obj) = row.as_object_mut() {
                obj.remove("consumer");
                obj.insert("subject".into(), serde_json::json!(subject));
                obj.insert("affected_function_count".into(), serde_json::json!(consumers.len()));
                obj.insert("affected_functions".into(), serde_json::json!(consumers));
                obj.insert("root_policies".into(), serde_json::json!(policies));
            }
            rows.push(row);
        }
    }
    let file_rows: Vec<serde_json::Value> = finding_projection
        .files
        .iter()
        .map(|file| {
            serde_json::json!({
                "record_index": file.record_index,
                "file": file.file,
                "functions": file.functions,
                "premise_coverage": file.premise_coverage,
                "findings": findings_by_file.get(&file.file).cloned().unwrap_or_default(),
            })
        })
        .collect();

    let mut project_terminal_statuses: BTreeMap<String, usize> = BTreeMap::new();
    let mut project_function_statuses: BTreeMap<String, usize> = BTreeMap::new();
    let mut project_definite_artifacts = BTreeSet::new();
    let mut project_possible_artifacts = BTreeSet::new();
    for query in &query_rows {
        if let Some(status) = query.get("status").and_then(|value| value.as_str()) {
            *project_terminal_statuses.entry(status.to_string()).or_default() += 1;
        }
    }
    for function in &function_rows {
        if let Some(status) = function.get("status").and_then(|value| value.as_str()) {
            *project_function_statuses.entry(status.to_string()).or_default() += 1;
        }
        if let Some(artifacts) =
            function.get("definite_artifacts").and_then(|value| value.as_array())
        {
            project_definite_artifacts
                .extend(artifacts.iter().filter_map(|value| value.as_str()).map(str::to_string));
        }
        if let Some(artifacts) =
            function.get("possible_artifacts").and_then(|value| value.as_array())
        {
            project_possible_artifacts
                .extend(artifacts.iter().filter_map(|value| value.as_str()).map(str::to_string));
        }
    }
    project_possible_artifacts.retain(|artifact| !project_definite_artifacts.contains(artifact));
    let project_status = if project_function_statuses.len() == 1
        && project_function_statuses.contains_key("NotApplicable")
    {
        "NotApplicable"
    } else if project_function_statuses.contains_key("Overapproximated") {
        "Overapproximated"
    } else if project_function_statuses.contains_key("Partial")
        || project_function_statuses.contains_key("Ungrounded")
    {
        "Partial"
    } else {
        "Complete"
    };

    // True roots of the observed proof: functions that no observed call site
    // targets. Every other function's proof is reached from these by
    // traversal, so they are the default root set at project scope.
    let called: BTreeSet<String> = records
        .iter()
        .flat_map(|record| record.functions.iter())
        .flat_map(|function| function.call_sites.iter())
        .filter_map(|(_, _, callee)| callee.clone())
        .collect();
    let call_graph_roots: Vec<String> = records
        .iter()
        .flat_map(|record| record.functions.iter())
        .map(|function| function.fun.clone())
        .collect::<BTreeSet<_>>()
        .difference(&called)
        .cloned()
        .collect();

    serde_json::json!({
        // 0.2: finding vocabulary of `PROOF_COVERAGE_FINDINGS.md` §2, and
        // `functions[].findings` is now the root-scoped survivor set. The old
        // `uncovered-premise` / `vacuous-obligation` names are gone with no
        // aliases, so a stale consumer fails on the version rather than
        // silently reading changed semantics.
        "schema": "verus-proof-coverage-report/0.2",
        "finding_vocabulary": "PROOF_COVERAGE_FINDINGS.md#2",
        "level": if records.len() > 1 { "project" } else { "crate" },
        "record_count": records.len(),
        "record_ids": records.iter().map(|record| record.record_id.clone()).collect::<Vec<_>>(),
        "record_versions": records
            .iter()
            .map(|record| record.artifact_version.clone())
            .collect::<BTreeSet<_>>(),
        "call_policy": match policy {
            CallPolicy::Opaque => "opaque",
            CallPolicy::Modular => "modular",
        },
        "semantics": {
            "definite": "grounded vertices in observed support witnesses",
            "possible": "scope overapproximation at unmeasured evidence boundaries",
            "calls": if policy == CallPolicy::Opaque {
                "intraprocedural: stop at imported call postconditions after same-call precondition checks"
            } else {
                "modular: cross call-local contract certification"
            },
        },
        "project": {
            "status": project_status,
            // True roots of the observed proof: functions that no observed
            // call site targets. Every other function's proof is reached from
            // these by traversal, so they are the default root set for a
            // project-scope analysis.
    "call_graph_roots": call_graph_roots,
            "terminal_statuses": project_terminal_statuses,
            "function_statuses": project_function_statuses,
            "definite_artifacts": project_definite_artifacts,
            "possible_artifacts": project_possible_artifacts,
        },
        // Query-scope observations, one row per (source fact, terminal). These
        // are *not* findings: `PROOF_COVERAGE.md` §7 is explicit that summing
        // available-not-observed across queries is meaningless, and a single
        // fact commonly appears here once per terminal. The findings are the
        // root-scoped survivors on `functions[]` and `files[]`. Named for its
        // scope so it cannot be mistaken for a finding count.
        "query_observations": finding_projection.queries,
        "analysis_coverage": projection::analysis_coverage(records),
        "files": file_rows,
        "queries": query_rows,
        "functions": function_rows,
    })
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let split = args.iter().position(|a| {
        matches!(
            a.as_str(),
            "summary"
                | "backward"
                | "forward"
                | "counterfactual"
                | "pulse"
                | "vertices"
                | "findings"
                | "explain"
                | "targets"
                | "unlicensed"
                | "slice"
                | "study"
                | "impact"
                | "report"
                | "project"
        )
    });
    let Some(split) = split else {
        eprintln!(
            "usage: pc-analyze <record.json>... <summary|backward|forward|counterfactual|vertices|findings|targets|slice|study|impact|report|project> [args]"
        );
        std::process::exit(2);
    };
    let (files, cmd) = args.split_at(split);
    if files.is_empty() {
        eprintln!("no record files given");
        std::process::exit(2);
    }
    let record_texts: Vec<(String, String)> = files
        .iter()
        .map(|f| {
            let text =
                std::fs::read_to_string(f).unwrap_or_else(|e| panic!("cannot read {}: {}", f, e));
            (f.clone(), text)
        })
        .collect();
    // One schema, one parse: the audit and the analyzer share the record type,
    // so a record cannot be read into two views that disagree.
    let records: Vec<CoverageRecord> = record_texts
        .iter()
        .map(|(file, text)| {
            let value: serde_json::Value = serde_json::from_str(text)
                .unwrap_or_else(|e| panic!("cannot parse {} for identity: {}", file, e));
            if let Err(violation) = proof_coverage::audit::verify_record_id(&value) {
                eprintln!("RECORD INVARIANT VIOLATION in {}: {}", file, violation);
                std::process::exit(1);
            }
            let record: CoverageRecord = serde_json::from_str(text)
                .unwrap_or_else(|e| panic!("cannot parse {}: {}", file, e));
            let findings = proof_coverage::audit::audit(&record, &proof_coverage::rules::lookup);
            if !findings.violations.is_empty() {
                for violation in &findings.violations {
                    eprintln!("RECORD INVARIANT VIOLATION in {}: {}", file, violation);
                }
                std::process::exit(1);
            }
            record
        })
        .collect();
    let g = analysis::build(&records);
    let violations = g.check();
    if !violations.is_empty() {
        for v in &violations {
            eprintln!("GRAPH INVARIANT VIOLATION: {}", v);
        }
        std::process::exit(1);
    }

    match cmd[0].as_str() {
        "summary" => {
            let count = |k: analysis::ArcKind| g.arcs.iter().filter(|a| a.kind == k).count();
            println!(
                "typed graph: {} arcs (SupportedBy {}, TerminalOf {}, CertifiedBy {}, Aggregates {}, ObservedInBatch {}), {} vertices",
                g.arcs.len(),
                count(analysis::ArcKind::SupportedBy),
                count(analysis::ArcKind::TerminalOf),
                count(analysis::ArcKind::CertifiedBy),
                count(analysis::ArcKind::Aggregates),
                count(analysis::ArcKind::ObservedInBatch),
                g.vertex_info.len(),
            );
            println!(
                "{} premises, {} obligations ({} spec, {} unmeasured), {} covered labels, {} vacuous",
                g.premises.len(),
                g.obligations.len(),
                g.spec_obligations.len(),
                g.unmeasured.len(),
                g.covered.len(),
                g.vacuous.len()
            );
            for n in &g.induction_notes {
                println!("induction: {}", n);
            }
            if !g.vacuous.is_empty() {
                println!("vacuous obligations:");
                for v in &g.vacuous {
                    println!("  {}", g.display(v));
                }
            }
        }
        "backward" => {
            let start = &cmd[1];
            let closure = g.backward(start);
            println!("backward closure of {} ({} vertices):", start, closure.len());
            for v in &closure {
                if v != start {
                    println!("  {}", g.display(v));
                }
            }
        }
        "forward" => {
            let mut base: BTreeSet<String> = g.roots();
            base.extend(cmd[1..].iter().cloned());
            let derived = g.forward(&base);
            println!("obligations derivable from roots ∪ {:?}:", cmd[1..].to_vec());
            for o in &g.obligations {
                if derived.contains(o) {
                    println!("  {}", g.display(o));
                }
            }
        }
        "counterfactual" => {
            let removed = &cmd[1];
            let broken = g.ablate(removed);
            if broken.is_empty() {
                println!(
                    "ablating {} breaks no surviving obligation (no known downstream dependence)",
                    removed
                );
            } else {
                println!("ablating {} breaks (no known alternative support):", removed);
                for o in &broken {
                    println!("  {}", g.display(o));
                }
            }
        }
        "pulse" => {
            eprintln!(
                "`pulse` is not part of the v0.1 coverage surface; use `findings` or `report`"
            );
            std::process::exit(2);
        }
        "explain" => {
            print!("{}", g.explain(&cmd[1]));
        }
        // Which constructs the licensing rules do not model, from the record.
        //
        // A premise with no licensing in-edge is a *root*: the analysis takes
        // it on trust and never asks what established it. Some roots are
        // correct — a function's own `requires`, an ambient axiom, control and
        // data flow of the body. A root that is really an assumption exported
        // by a checked construct is a missing rule, and it fails open: every
        // fact that supported only the discharge of that export drops out of
        // every slice and is reported unused.
        //
        // For each unlicensed group this prints what the record already
        // carries, which is what decides where the work lives. A rule can
        // quantify over `rf.at(artifact, role)`, so it needs a shared artifact
        // identity and a role that distinguishes the export from its check.
        "unlicensed" => {
            let roots = g.roots();
            let mut expected: BTreeMap<String, usize> = BTreeMap::new();
            let mut untyped: BTreeMap<String, usize> = BTreeMap::new();
            let mut no_rule: BTreeMap<String, UnlicensedGroup> = BTreeMap::new();
            let mut not_fired: BTreeMap<String, UnlicensedGroup> = BTreeMap::new();
            for vertex in &roots {
                let Some(info) = g.vertex_info.get(vertex) else { continue };
                let Some(emission) = &info.emission else { continue };
                let (bucket, positioned) = root_expectation(emission);
                let key = emission_group(emission);
                let group = match bucket {
                    RootBucket::Expected => {
                        *expected.entry(key).or_default() += 1;
                        continue;
                    }
                    RootBucket::Untyped => {
                        *untyped.entry(key).or_default() += 1;
                        continue;
                    }
                    RootBucket::NoRule => no_rule.entry(key).or_default(),
                    RootBucket::RuleDidNotFire => not_fired.entry(key).or_default(),
                };
                group.rows += 1;
                group.with_artifact += info.artifact.is_some() as usize;
                group.with_node += info.node.is_some() as usize;
                group.positioned = positioned;
                if let Some(fun) = &info.fun {
                    group.functions.insert(fun.clone());
                }
            }
            println!("proof-coverage-unlicensed 0.1");
            println!();
            println!("roots the analysis is right to trust:");
            for (role, n) in &expected {
                println!("  {n:6}  {role}");
            }
            println!();
            if !untyped.is_empty() {
                println!("roots whose only provenance is the lowering template:");
                for (role, n) in &untyped {
                    println!("  {n:6}  {role}");
                }
                println!();
            }
            if no_rule.is_empty() && not_fired.is_empty() {
                println!("every exported assumption is licensed");
                return;
            }
            let table = |title: &str, note: &[&str], rows: &BTreeMap<String, UnlicensedGroup>| {
                if rows.is_empty() {
                    return;
                }
                println!("{title}");
                for line in note {
                    println!("  {line}");
                }
                println!(
                    "  {:>6}  {:>8}  {:>8}  {:>10}  {:>4}  {}",
                    "rows", "artifact", "cfg node", "positioned", "fns", "construct"
                );
                for (role, gr) in rows {
                    println!(
                        "  {:>6}  {:>8}  {:>8}  {:>10}  {:>4}  {}",
                        gr.rows,
                        gr.with_artifact,
                        gr.with_node,
                        if gr.positioned { "yes" } else { "no" },
                        gr.functions.len(),
                        role
                    );
                }
                println!();
            };
            table(
                "no licensing rule for the construct:",
                &[
                    "A rule quantifies over (artifact, role). `artifact` 0 means there is no",
                    "identity to pair the export with its check; `positioned` no means the role",
                    "does not say which is which. Both are record relations to add, after which",
                    "the rule is an instance of the checked-export shape.",
                ],
                &no_rule,
            );
            table(
                "rule exists, but its join did not fire for these rows:",
                &[
                    "Nothing to model. `artifact` or `cfg node` short of `rows` names the join",
                    "that failed; where both are present, the pairing itself did not complete.",
                ],
                &not_fired,
            );
            let mut affected: BTreeSet<&String> = BTreeSet::new();
            for gr in no_rule.values().chain(not_fired.values()) {
                affected.extend(gr.functions.iter());
            }
            println!("{} functions have findings that fail open:", affected.len());
            for fun in affected.iter().take(40) {
                println!("  {}", g.display_function(fun));
            }
            if affected.len() > 40 {
                println!("  ... and {} more", affected.len() - 40);
            }
        }
        "targets" => {
            let filter = cmd.get(1).map(String::as_str).unwrap_or("");
            let rows: Vec<_> = targets(&records)
                .into_iter()
                .filter(|row| {
                    filter.is_empty()
                        || row.fun.contains(filter)
                        || row.target.contains(filter)
                        || row.parent.as_deref().unwrap_or("").contains(filter)
                })
                .collect();
            let mut slices = g.backward_slices(
                rows.iter().filter(|row| !not_applicable(row)).map(|row| row.target.clone()),
                SliceOptions { calls: CallPolicy::Opaque },
            );
            let fail_open = fail_open_roots(&g);
            for row in rows {
                let status = if not_applicable(&row) {
                    "NotApplicable"
                } else {
                    let slice =
                        slices.remove(&row.target).expect("target slicer omitted requested target");
                    slice_status(&g, &slice, &fail_open)
                };
                println!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    row.target,
                    row.fun,
                    row.parent.as_deref().unwrap_or("-"),
                    row.span,
                    row.terminal_path.as_deref().unwrap_or("-"),
                    status,
                    row.desc,
                );
            }
        }
        "slice" => {
            let Some(target) = cmd.get(1) else {
                eprintln!("slice requires a target; use `targets` to list source-level terminals");
                std::process::exit(2);
            };
            let policy = call_policy(cmd.get(2));
            let slice = g.backward_slice(target, SliceOptions { calls: policy });
            println!(
                "slice {} — {} — calls={}",
                target,
                slice_status(&g, &slice, &fail_open_roots(&g)),
                if policy == CallPolicy::Opaque { "opaque" } else { "modular" },
            );
            println!("definite ({}):", slice.definite.len());
            for vertex in &slice.definite {
                println!("  {}", g.display(vertex));
            }
            println!("possible ({}):", slice.possible.len());
            for vertex in &slice.possible {
                println!("  {}", g.display(vertex));
            }
            println!("boundaries ({}):", slice.boundaries.len());
            for boundary in &slice.boundaries {
                println!("  {}", boundary_json(boundary));
            }
        }
        "study" => {
            let filter = cmd.get(1).map(String::as_str).unwrap_or("");
            let policy = call_policy(cmd.get(2));
            research_text(&g, &records, filter, policy);
        }
        "impact" => {
            let Some(target) = cmd.get(1) else {
                eprintln!("impact requires a target artifact id or vertex");
                std::process::exit(2);
            };
            let policy = call_policy(cmd.get(2));
            impact_text(&g, &records, target, policy);
        }
        "report" => {
            let policy = call_policy(cmd.get(1));
            println!(
                "{}",
                serde_json::to_string_pretty(&report_json(&g, &records, policy)).unwrap()
            );
        }
        "project" => {
            let policy = match cmd.get(1) {
                None => CallPolicy::Modular,
                arg => call_policy(arg),
            };
            println!(
                "{}",
                serde_json::to_string_pretty(&report_json(&g, &records, policy)).unwrap()
            );
        }
        "findings" => {
            let policy = call_policy(cmd.iter().skip(1).find(|a| !a.starts_with("--")));
            print_findings_report(
                &report_json(&g, &records, policy),
                cmd.iter().any(|a| a == "--all"),
            );
        }
        "vertices" => {
            let filter = cmd.get(1).map(|s| s.as_str()).unwrap_or("");
            for (v, _) in &g.vertex_info {
                if v.contains(filter) {
                    println!("{}  ->  {}", v, g.display(v));
                }
            }
        }
        other => {
            eprintln!("unknown command {}", other);
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AssumptionSource, CoverageRecord, assumption_source, function_status, report_json,
    };
    use proof_coverage::analysis::{self, CallPolicy};
    use serde_json::{Value, json};
    use std::collections::BTreeMap;

    fn artifact(id: &str, kind: &str, span: &str) -> Value {
        json!({
            "id": id,
            "kind": kind,
            "owner": "crate::f",
            "span": span,
        })
    }

    fn occurrence(
        role: &str,
        label: &str,
        origin_kind: &str,
        artifact: Option<&str>,
        span: &str,
        phase: &str,
    ) -> Value {
        occurrence_with(role, label, origin_kind, "test", artifact, span, phase)
    }

    fn occurrence_with(
        role: &str,
        label: &str,
        origin_kind: &str,
        detail: &str,
        artifact: Option<&str>,
        span: &str,
        phase: &str,
    ) -> Value {
        // Tests name the protocol position by its rendered phase; the record
        // carries the typed role it renders from.
        let emission = match phase {
            "function.ensures" => json!({"kind": "function_ensures"}),
            "function.requires" => json!({"kind": "function_requires", "clause": 0}),
            "assert.check" => json!({"kind": "assertion", "point": "check"}),
            "assert.establish" => json!({"kind": "assertion", "point": "establish"}),
            "user.assume" => json!({"kind": "user_assumption"}),
            "" => Value::Null,
            other => panic!("test phase {other} has no role mapping"),
        };
        json!({
            // Structural placement, part of the occurrence's identity. These
            // tests do not key on it, so the unique label stands in.
            "path": label,
            "role": role,
            "carrier": if role == "premise" { "assume" } else { "assert" },
            "origin": {"kind": origin_kind, "detail": detail},
            "emission": emission,
            "label": label,
            "artifact": artifact,
            "span": span,
        })
    }

    /// The solver configuration the schema requires of every query. Its
    /// contents are irrelevant to these tests, but the record has no notion
    /// of a query without one.
    fn solver_config() -> Value {
        json!({
            "solver": "z3",
            "options": [],
            "rlimit": 0,
            "single_check_query": false,
            "ignore_unexpected_smt": false,
            "debug": false,
        })
    }

    fn batch(occurrences: Vec<Value>) -> Value {
        let labels = occurrences
            .iter()
            .filter_map(|occurrence| occurrence["label"].as_str())
            .collect::<Vec<_>>();
        json!({
            "id": 0,
            "family": "batch",
            "solver_context": 0,
            "solver_config": solver_config(),
            "fun": "crate::f",
            "desc": "check",
            "span": "f.rs:1",
            "ambient_batches": 0,
            "occurrences": occurrences,
            "results": [],
            "core": labels,
            "shadow_result": "valid",
            "evidence_backend": "unsat_core",
        })
    }

    fn focused(
        id: u64,
        target: &str,
        parent: &str,
        available: Vec<&str>,
        core: Option<Vec<&str>>,
        span: &str,
    ) -> Value {
        json!({
            "id": id,
            "family": "focused",
            "solver_context": 0,
            "solver_config": solver_config(),
            "fun": "crate::f",
            "desc": "focused check",
            "span": span,
            "ambient_batches": 0,
            "terminal_path": format!("q.a{}", id - 1),
            "target_label": target,
            "parent_obligation_label": parent,
            "available": available,
            "occurrences": [],
            "results": [],
            "core": core,
            "shadow_result": if core.is_some() { "valid" } else { "canceled" },
            "evidence_backend": if core.is_some() { Some("unsat_core") } else { None },
        })
    }

    fn not_applicable_focused(id: u64, target: &str, parent: &str, span: &str) -> Value {
        let mut query = focused(id, target, parent, vec![target], None, span);
        query["shadow_result"] = json!("canonical_not_applicable");
        query
    }

    fn record(queries: Vec<Value>, artifacts: Vec<Value>) -> CoverageRecord {
        serde_json::from_value(json!({
            "schema": proof_coverage::record::SCHEMA,
            "artifact_version": "0.1",
            "functions": [],
            "queries": queries,
            "ambients": [],
            "artifacts": artifacts,
            "refinements": [],
            "derivations": [],
            "summary": {
                "queries": 0,
                "premises": 0,
                "obligations": 0,
                "unresolved_premises": 0,
                "unresolved_obligations": 0,
                "unresolved_buckets": [],
                "results": [],
            },
            "record_id": format!("pc_r%{}", "0".repeat(64)),
        }))
        .unwrap()
    }

    fn report(record: CoverageRecord) -> Value {
        let records = vec![record];
        let graph = analysis::build(&records);
        report_json(&graph, &records, CallPolicy::Opaque)
    }

    fn finding_kinds(value: &Value) -> Vec<&str> {
        value.as_array().unwrap().iter().map(|finding| finding["kind"].as_str().unwrap()).collect()
    }

    /// Rooted section: postcondition terminals are the roots; an artifact
    /// observed only by an auxiliary obligation becomes `auxiliary-only-fact`
    /// (`PROOF_COVERAGE_FINDINGS.md` §2.2), the specialization emitted instead
    /// of a generic unused-fact kind, and it names the observing terminal. The
    /// specialization never suppresses the finding.
    #[test]
    fn rooted_classification_separates_goal_and_auxiliary_support() {
        let aux_target = "pc%0%t%2%0";
        let root_target = "pc%0%t%3%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%1",
                        "source",
                        Some("crate::f#req[1]"),
                        "f.rs:3:5",
                        "function.requires",
                    ),
                    occurrence_with(
                        "obligation",
                        "pc%0%2",
                        "generated",
                        "arith_overflow_check",
                        None,
                        "f.rs:5:5",
                        "",
                    ),
                    occurrence_with(
                        "obligation",
                        "pc%0%3",
                        "source",
                        "ensures",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    aux_target,
                    "pc%0%2",
                    vec!["pc%0%0", "pc%0%1", aux_target],
                    Some(vec!["pc%0%1", aux_target]),
                    "f.rs:5:5",
                ),
                focused(
                    2,
                    root_target,
                    "pc%0%3",
                    vec!["pc%0%0", "pc%0%1", root_target],
                    Some(vec!["pc%0%0", root_target]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#req[1]", "requires_clause", "f.rs:3:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        let rooted = &report["functions"][0]["rooted"];
        assert_eq!(rooted["policy"], "opaque");
        assert_eq!(
            rooted["roots"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| r["target"].as_str().unwrap())
                .collect::<Vec<_>>(),
            vec![root_target],
            "only the postcondition terminal is a default root"
        );
        let classification = rooted["classification"].as_array().unwrap();
        assert_eq!(classification.len(), 1);
        assert_eq!(classification[0]["artifact"], "crate::f#req[0]");
        assert_eq!(classification[0]["class"], "direct-support");
        assert_eq!(classification[0]["locality"], "local");
        assert_eq!(finding_kinds(&rooted["findings"]), vec!["auxiliary-only-fact"]);
        assert_eq!(rooted["findings"][0]["source"]["artifact"], "crate::f#req[1]");
        let aux = rooted["findings"][0]["auxiliary_support"].as_array().unwrap();
        assert_eq!(aux.len(), 1);
        assert_eq!(aux[0]["terminal"], aux_target);
        assert_eq!(aux[0]["obligation_detail"], "arith_overflow_check");
        let witnesses = rooted["witnesses"].as_array().unwrap();
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0]["root"], root_target);
        assert_eq!(witnesses[0]["observed"], true);
    }

    /// Rooted section: a vacuous root exposes its contradiction witness as
    /// direct-contradiction, keeps the vacuous-terminal finding, and gets no
    /// slice-derived support.
    #[test]
    fn rooted_vacuous_root_keeps_contradiction_witness() {
        let target = "pc%0%t%1%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence_with(
                        "obligation",
                        "pc%0%1",
                        "source",
                        "ensures",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%1",
                    vec!["pc%0%0", target],
                    Some(vec!["pc%0%0"]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        let rooted = &report["functions"][0]["rooted"];
        let witnesses = rooted["witnesses"].as_array().unwrap();
        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses[0]["observed"], false);
        let classification = rooted["classification"].as_array().unwrap();
        assert_eq!(classification.len(), 1);
        assert_eq!(classification[0]["artifact"], "crate::f#req[0]");
        assert_eq!(classification[0]["class"], "direct-contradiction");
        assert_eq!(finding_kinds(&rooted["findings"]), vec!["vacuous-postcondition"]);
        assert_eq!(rooted["steps"], json!([]));
    }

    #[test]
    fn function_status_preserves_incomplete_terminal_states() {
        let statuses = BTreeMap::from([("NotApplicable", 2)]);
        assert_eq!(function_status(&statuses), "NotApplicable");

        let statuses = BTreeMap::from([("Complete", 1), ("Ungrounded", 1)]);
        assert_eq!(function_status(&statuses), "Partial");

        let statuses = BTreeMap::from([("Complete", 1), ("Overapproximated", 1)]);
        assert_eq!(function_status(&statuses), "Overapproximated");

        let statuses = BTreeMap::from([("Ungrounded", 2)]);
        assert_eq!(function_status(&statuses), "Ungrounded");
    }

    #[test]
    fn all_not_applicable_terminals_remain_at_function_and_project_scope() {
        let first = "pc%0%t%0%0";
        let second = "pc%0%t%1%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "obligation",
                        "pc%0%0",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%1",
                        "source",
                        Some("crate::f#ens[1]"),
                        "f.rs:9:5",
                        "function.ensures",
                    ),
                ]),
                not_applicable_focused(1, first, "pc%0%0", "f.rs:8:5"),
                not_applicable_focused(2, second, "pc%0%1", "f.rs:9:5"),
            ],
            vec![
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
                artifact("crate::f#ens[1]", "ensures_clause", "f.rs:9:5"),
            ],
        );

        let report = report(record);
        assert_eq!(report["queries"][0]["status"], "NotApplicable");
        assert_eq!(report["queries"][1]["status"], "NotApplicable");
        assert_eq!(report["functions"].as_array().unwrap().len(), 1);
        assert_eq!(report["functions"][0]["function"], "crate::f");
        assert_eq!(report["functions"][0]["status"], "NotApplicable");
        assert_eq!(report["functions"][0]["terminal_statuses"]["NotApplicable"], 2);
        assert_eq!(report["functions"][0]["coverage_terminal_counts"]["not-applicable"], 2);
        assert_eq!(report["functions"][0]["terminals"], json!([first, second]));
        assert_eq!(report["functions"][0]["completeness"]["evidence"], "NotApplicable");
        assert_eq!(report["project"]["status"], "NotApplicable");
        assert_eq!(report["project"]["terminal_statuses"]["NotApplicable"], 2);
        assert_eq!(report["project"]["function_statuses"]["NotApplicable"], 1);
        assert_eq!(report["query_observations"], json!([]));
    }

    #[test]
    fn not_applicable_terminal_does_not_replace_measured_findings() {
        let canonical_target = "pc%0%t%1%0";
        let measured_target = "pc%0%t%2%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%1",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%2",
                        "source",
                        Some("crate::f#ens[1]"),
                        "f.rs:9:5",
                        "function.ensures",
                    ),
                ]),
                not_applicable_focused(1, canonical_target, "pc%0%1", "f.rs:8:5"),
                focused(
                    2,
                    measured_target,
                    "pc%0%2",
                    vec!["pc%0%0", measured_target],
                    Some(vec![measured_target]),
                    "f.rs:9:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
                artifact("crate::f#ens[1]", "ensures_clause", "f.rs:9:5"),
            ],
        );

        let report = report(record);
        assert_eq!(report["functions"].as_array().unwrap().len(), 1);
        assert_eq!(report["functions"][0]["terminal_statuses"]["NotApplicable"], 1);
        assert_ne!(report["functions"][0]["status"], "NotApplicable");
        assert_ne!(report["project"]["status"], "NotApplicable");
        assert_eq!(finding_kinds(&report["query_observations"]), vec!["available-not-observed"]);
        assert_eq!(
            finding_kinds(&report["functions"][0]["findings"]),
            vec!["goal-unused-precondition"]
        );
        assert_eq!(
            finding_kinds(&report["files"][0]["findings"]),
            vec!["goal-unused-precondition"]
        );
    }

    #[test]
    fn report_derives_uncovered_source_premises_from_complete_measurement() {
        let target = "pc%0%t%2%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%1",
                        "source",
                        Some("crate::f#req[1]"),
                        "f.rs:3:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%2",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%2",
                    vec!["pc%0%0", "pc%0%1", target],
                    Some(vec!["pc%0%0", target]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#req[1]", "requires_clause", "f.rs:3:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        assert_eq!(finding_kinds(&report["query_observations"]), vec!["available-not-observed"]);
        assert_eq!(report["query_observations"][0]["source"]["artifact"], "crate::f#req[1]");
        assert_eq!(report["query_observations"][0]["premise_refs"], json!(["pc%0%1"]));
        assert_eq!(
            report["functions"][0]["premise_coverage"]
                .as_array()
                .unwrap()
                .iter()
                .map(|coverage| coverage["status"].as_str().unwrap())
                .collect::<Vec<_>>(),
            vec!["observed-all", "observed-none"]
        );
        assert_eq!(
            finding_kinds(&report["functions"][0]["findings"]),
            vec!["goal-unused-precondition"]
        );
        assert_eq!(
            finding_kinds(&report["files"][0]["findings"]),
            vec!["goal-unused-precondition"]
        );
    }

    #[test]
    fn unresolved_available_source_row_suppresses_absence_findings() {
        let target = "pc%0%t%3%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%1",
                        "source",
                        Some("crate::f#req[1]"),
                        "f.rs:3:5",
                        "function.requires",
                    ),
                    occurrence("premise", "pc%0%2", "unresolved", None, "f.rs:4:5", ""),
                    occurrence(
                        "obligation",
                        "pc%0%3",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%3",
                    vec!["pc%0%0", "pc%0%1", "pc%0%2", target],
                    Some(vec!["pc%0%0", target]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#req[1]", "requires_clause", "f.rs:3:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        assert_eq!(report["query_observations"], json!([]));
        assert!(
            report["functions"][0]["premise_coverage"]
                .as_array()
                .unwrap()
                .iter()
                .all(|coverage| coverage["status"] == "incomplete")
        );
        assert_eq!(report["functions"][0]["findings"], json!([]));
    }

    #[test]
    fn vacuity_requires_valid_measured_evidence() {
        let measured = "pc%0%t%1%0";
        let unmeasured = "pc%0%t%1%1";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%1",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    measured,
                    "pc%0%1",
                    vec!["pc%0%0", measured],
                    Some(vec!["pc%0%0"]),
                    "f.rs:8:5",
                ),
                focused(2, unmeasured, "pc%0%1", vec!["pc%0%0", unmeasured], None, "f.rs:8:5"),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        assert_eq!(finding_kinds(&report["query_observations"]), vec!["vacuous-terminal"]);
        assert_eq!(report["query_observations"][0]["terminal"]["terminal_ref"], measured);
        assert_eq!(report["functions"][0]["premise_coverage"][0]["status"], "incomplete");
    }

    #[test]
    fn vacuous_terminal_can_also_have_an_uncovered_premise() {
        let target = "pc%0%t%3%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%1",
                        "source",
                        Some("crate::f#req[1]"),
                        "f.rs:3:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%2",
                        "source",
                        Some("crate::f#req[2]"),
                        "f.rs:4:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%3",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%3",
                    vec!["pc%0%0", "pc%0%1", "pc%0%2", target],
                    Some(vec!["pc%0%0", "pc%0%1"]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#req[1]", "requires_clause", "f.rs:3:5"),
                artifact("crate::f#req[2]", "requires_clause", "f.rs:4:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        assert_eq!(
            finding_kinds(&report["query_observations"]),
            vec!["available-not-observed", "vacuous-terminal"]
        );
        assert_eq!(
            finding_kinds(&report["functions"][0]["findings"]),
            vec!["vacuous-postcondition"]
        );
        assert_eq!(report["functions"][0]["secondary_observations"].as_array().unwrap().len(), 1);
        assert_eq!(
            report["functions"][0]["secondary_observations"][0]["secondary_reason"],
            "all-selected-roots-vacuous"
        );
    }

    #[test]
    fn all_measured_assertion_root_is_standalone_not_unused() {
        let target = "pc%0%t%1%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence_with(
                        "premise",
                        "pc%0%0",
                        "derived",
                        "sst:Assert",
                        Some("crate::f#assert.src0"),
                        "f.rs:5:5",
                        "assert.establish",
                    ),
                    occurrence_with(
                        "obligation",
                        "pc%0%1",
                        "source",
                        "assertion",
                        Some("crate::f#assert.src0"),
                        "f.rs:5:5",
                        "assert.check",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%1",
                    vec!["pc%0%0", target],
                    Some(vec![target]),
                    "f.rs:5:5",
                ),
            ],
            vec![artifact("crate::f#assert.src0", "assertion", "f.rs:5:5")],
        );

        let report = report(record);
        let function = &report["functions"][0];
        assert_eq!(function["root_policy"], "all-measured");
        assert_eq!(function["findings"], json!([]));
        assert_eq!(function["secondary_observations"].as_array().unwrap().len(), 1);
        assert_eq!(
            function["secondary_observations"][0]["secondary_reason"],
            "selected-root-is-own-proof-obligation"
        );
    }

    #[test]
    fn trusted_dependency_in_direct_contradiction_is_reported() {
        let target = "pc%0%t%1%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence_with(
                        "premise",
                        "pc%0%0",
                        "source",
                        "sst:UserAssume",
                        Some("crate::f#assume.src0"),
                        "f.rs:5:5",
                        "user.assume",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%1",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%1",
                    vec!["pc%0%0", target],
                    Some(vec!["pc%0%0"]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#assume.src0", "assumption", "f.rs:5:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        let findings = report["functions"][0]["findings"].as_array().unwrap();
        assert_eq!(
            finding_kinds(&report["functions"][0]["findings"]),
            vec!["vacuous-postcondition", "trusted-dependency"]
        );
        let trust = findings.iter().find(|row| row["claim"] == "trust").unwrap();
        assert_eq!(trust["trust"], "user-assumption-or-admission");
    }

    #[test]
    fn source_assumption_classifier_separates_protocol_hypotheses() {
        let path = std::env::temp_dir()
            .join(format!("pc-analyze-assumption-source-{}.rs", std::process::id()));
        std::fs::write(
            &path,
            "assume(false);\nadmit();\nrequire(pre.ok);\nremove token -= {()};\n",
        )
        .unwrap();
        let span = |line: usize| format!("{}:{line}:1: {line}:2", path.display());

        assert!(matches!(
            assumption_source(Some(&span(1))),
            AssumptionSource::Explicit("user-assumption")
        ));
        assert!(matches!(
            assumption_source(Some(&span(2))),
            AssumptionSource::Explicit("admission")
        ));
        assert!(matches!(
            assumption_source(Some(&span(3))),
            AssumptionSource::OtherSourceConstruct
        ));
        assert!(matches!(
            assumption_source(Some(&span(4))),
            AssumptionSource::OtherSourceConstruct
        ));
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn mixed_terminal_observation_is_not_promoted_to_function_unused() {
        let first = "pc%0%t%1%0";
        let second = "pc%0%t%2%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%1",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%2",
                        "source",
                        Some("crate::f#ens[1]"),
                        "f.rs:9:5",
                        "function.ensures",
                    ),
                ]),
                focused(1, first, "pc%0%1", vec!["pc%0%0", first], Some(vec![first]), "f.rs:8:5"),
                focused(
                    2,
                    second,
                    "pc%0%2",
                    vec!["pc%0%0", second],
                    Some(vec!["pc%0%0", second]),
                    "f.rs:9:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
                artifact("crate::f#ens[1]", "ensures_clause", "f.rs:9:5"),
            ],
        );

        let report = report(record);
        assert_eq!(finding_kinds(&report["query_observations"]), vec!["available-not-observed"]);
        assert_eq!(report["functions"][0]["premise_coverage"][0]["status"], "observed-some");
        assert_eq!(report["functions"][0]["findings"], json!([]));
    }

    #[test]
    fn artifacts_sharing_a_source_span_remain_distinct() {
        let target = "pc%0%t%2%0";
        let record = record(
            vec![
                batch(vec![
                    occurrence(
                        "premise",
                        "pc%0%0",
                        "source",
                        Some("crate::f#req[0]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "premise",
                        "pc%0%1",
                        "source",
                        Some("crate::f#req[1]"),
                        "f.rs:2:5",
                        "function.requires",
                    ),
                    occurrence(
                        "obligation",
                        "pc%0%2",
                        "source",
                        Some("crate::f#ens[0]"),
                        "f.rs:8:5",
                        "function.ensures",
                    ),
                ]),
                focused(
                    1,
                    target,
                    "pc%0%2",
                    vec!["pc%0%0", "pc%0%1", target],
                    Some(vec!["pc%0%0", target]),
                    "f.rs:8:5",
                ),
            ],
            vec![
                artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#req[1]", "requires_clause", "f.rs:2:5"),
                artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
            ],
        );

        let report = report(record);
        assert_eq!(finding_kinds(&report["query_observations"]), vec!["available-not-observed"]);
        assert_eq!(report["query_observations"][0]["source"]["artifact"], "crate::f#req[1]");
    }

    #[test]
    fn multi_record_projection_does_not_merge_same_named_artifacts() {
        let make_record = |observed: bool| {
            let target = "pc%0%t%1%0";
            record(
                vec![
                    batch(vec![
                        occurrence(
                            "premise",
                            "pc%0%0",
                            "source",
                            Some("crate::f#req[0]"),
                            "f.rs:2:5",
                            "function.requires",
                        ),
                        occurrence(
                            "obligation",
                            "pc%0%1",
                            "source",
                            Some("crate::f#ens[0]"),
                            "f.rs:8:5",
                            "function.ensures",
                        ),
                    ]),
                    focused(
                        1,
                        target,
                        "pc%0%1",
                        vec!["pc%0%0", target],
                        Some(if observed { vec!["pc%0%0", target] } else { vec![target] }),
                        "f.rs:8:5",
                    ),
                ],
                vec![
                    artifact("crate::f#req[0]", "requires_clause", "f.rs:2:5"),
                    artifact("crate::f#ens[0]", "ensures_clause", "f.rs:8:5"),
                ],
            )
        };
        let records = vec![make_record(true), make_record(false)];
        let graph = analysis::build(&records);
        let report = report_json(&graph, &records, CallPolicy::Opaque);

        assert_eq!(finding_kinds(&report["query_observations"]), vec!["available-not-observed"]);
        assert_eq!(report["query_observations"][0]["source"]["record_index"], 1);
        assert_eq!(report["functions"].as_array().unwrap().len(), 2);
        assert_eq!(
            report["functions"]
                .as_array()
                .unwrap()
                .iter()
                .map(|function| function["record_index"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            vec![0, 1]
        );
    }
}
