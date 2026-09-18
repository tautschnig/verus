//! Executable audit of the model invariants (`PROOF_COVERAGE.md` §2)
//! over emitted records, plus join-quality measurements.
//!
//! Audits are the safety net for a design that recovers provenance by
//! inference: they cannot prove a classification correct, but they do prove
//! the record is internally consistent and that nothing was invented — every
//! core label was available, every reference resolves, labels are injective,
//! derivations are well-founded, and unsupported queries produce no evidence.
//!
//! Join quality is measured, not assumed: span collision rates bound how far
//! span-keyed projection (ProofPulse-style) could ever be trusted, and the
//! unresolved ledger bounds classification completeness per family.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

// The audit consumes `crate::record` directly, not a widened subset: an audit
// that cannot see the schema cannot detect a schema it disagrees with, and
// sharing the definition rules out phantom fields by construction.

use crate::record::{
    Artifact, ArtifactKind, Carrier, CoverageRecord, FunctionRecord, Occurrence, OriginKind,
    QueryFamily, QueryRecord, Role, SolverConfigRecord, Transform,
};

pub struct Findings {
    pub violations: Vec<String>,
    pub stats: Vec<(String, String)>,
}

fn audit_typed_artifact_join(
    query: &QueryRecord,
    occurrence_index: usize,
    occurrence: &Occurrence,
    artifact: &Artifact,
    refines: &std::collections::BTreeMap<&str, &str>,
) -> Vec<String> {
    let Some(join_rule) = occurrence.join_rule.as_deref() else {
        return Vec::new();
    };
    // Join type-checks quantify over the typed emission role: a join rule
    // may only attach an artifact whose kind the role admits.
    use crate::record::{ContractSection, EmissionRole as E};
    let role = occurrence.emission.as_ref();
    let expected_clause_kind = match join_rule {
        "join.clause_span" => match role {
            Some(E::FunctionEnsures) => Some(ArtifactKind::EnsuresClause),
            Some(E::LoopInvariant { .. }) => Some(ArtifactKind::LoopInvariantClause),
            _ => None,
        },
        "join.requires_index" | "join.emitted_clause"
            if matches!(role, Some(E::FunctionRequires { .. })) =>
        {
            Some(ArtifactKind::RequiresClause)
        }
        "join.emitted_clause" => match role {
            Some(E::LoopInvariant { .. }) => Some(ArtifactKind::LoopInvariantClause),
            _ => None,
        },
        "join.assert_site" => match role {
            Some(E::Assertion { .. }) => Some(ArtifactKind::Assertion),
            _ => None,
        },
        "join.type_invariant_fn" => {
            return match (role, artifact.kind) {
                (Some(E::TypeInvariant { .. }), ArtifactKind::Function) => Vec::new(),
                (role, kind) => vec![format!(
                    "q{} occ{}: {} joined {} artifact {} from role {:?}, expected a type \
                     invariant assumption joined to a function",
                    query.id, occurrence_index, join_rule, kind, artifact.id, role
                )],
            };
        }
        "join.statement_site" | "join.loop_condition" | "join.source_provenance" => {
            // Keyed on the emitting statement's CFG node (or the recorded
            // loop id), not on span: the artifact's span is the condition
            // expression, the occurrence's is the statement.
            let expected = match role {
                Some(E::UserAssumption) => Some(ArtifactKind::Assumption),
                // An assignment equality is either a written `let` or the
                // return lowering's binding; which one is decided by the CFG
                // node's kind, which this check does not reach, so both
                // statement kinds are admitted here.
                Some(E::AssignmentEquality)
                    if matches!(
                        artifact.kind,
                        ArtifactKind::Assignment | ArtifactKind::ReturnBinding
                    ) =>
                {
                    Some(artifact.kind)
                }
                Some(E::AssignmentEquality | E::MutationEquality) => Some(ArtifactKind::Assignment),
                Some(E::Fuel { site: crate::record::FuelSite::Statement }) => {
                    Some(ArtifactKind::Reveal)
                }
                Some(E::BranchCondition { .. }) => Some(ArtifactKind::BranchCondition),
                Some(E::LoopEntryCondition | E::LoopExitCondition) => {
                    Some(ArtifactKind::LoopCondition)
                }
                Some(E::Assertion { .. }) => Some(ArtifactKind::Assertion),
                Some(E::AssertForall { .. }) => Some(ArtifactKind::AssertForall),
                Some(E::TerminationCheck { .. }) => Some(ArtifactKind::DecreasesAggregate),
                _ => None,
            };
            return match expected {
                Some(kind) if artifact.kind != kind => vec![format!(
                    "q{} occ{}: {} joined {} artifact {}, expected {}",
                    query.id, occurrence_index, join_rule, artifact.kind, artifact.id, kind
                )],
                Some(_) if artifact.owner != query.fun => vec![format!(
                    "q{} occ{}: {} joined artifact {} owned by {}, expected {}",
                    query.id, occurrence_index, join_rule, artifact.id, artifact.owner, query.fun
                )],
                Some(_)
                    if join_rule == "join.statement_site"
                        && artifact.cfg_node.as_deref() != occurrence.node.as_deref() =>
                {
                    vec![format!(
                        "q{} occ{}: {} joined artifact {} at node {:?}, occurrence is at {:?}",
                        query.id,
                        occurrence_index,
                        join_rule,
                        artifact.id,
                        artifact.cfg_node,
                        occurrence.node
                    )]
                }
                Some(_) => Vec::new(),
                None => vec![format!(
                    "q{} occ{}: {} has no statement role ({:?})",
                    query.id, occurrence_index, join_rule, role
                )],
            };
        }
        "join.forall_site" => match role {
            Some(E::AssertForall { .. }) => Some(ArtifactKind::AssertForall),
            _ => None,
        },
        "join.trait_refinement" => {
            // Justified by the recorded impl -> trait relation, not by
            // relaxing the owner check.
            let expected = refines.get(query.fun.as_str()).copied();
            return match expected {
                Some(target) if artifact.owner == target => Vec::new(),
                Some(target) => vec![format!(
                    "q{} occ{}: {} joined artifact {} owned by {}, expected the refined \
                     trait method {}",
                    query.id, occurrence_index, join_rule, artifact.id, artifact.owner, target
                )],
                None => vec![format!(
                    "q{} occ{}: {} used but {} has no recorded trait refinement",
                    query.id, occurrence_index, join_rule, query.fun
                )],
            };
        }
        "join.lemma_clause_span" => match role {
            Some(E::AssertQuery { section: ContractSection::Requires, .. }) => {
                Some(ArtifactKind::LemmaRequiresClause)
            }
            Some(E::AssertQuery { section: ContractSection::Ensures, .. }) => {
                Some(ArtifactKind::LemmaEnsuresClause)
            }
            _ => None,
        },
        "join.contract_aggregate" => {
            let expected = match role.and_then(E::call_contract) {
                Some((ContractSection::Requires, Some(_))) => Some(ArtifactKind::RequiresAggregate),
                Some((ContractSection::Ensures, _)) => Some(ArtifactKind::EnsuresAggregate),
                _ => None,
            };
            return match expected {
                Some(kind) if artifact.kind == kind => Vec::new(),
                Some(kind) => vec![format!(
                    "q{} occ{}: {} joined {} artifact {}, expected {}",
                    query.id, occurrence_index, join_rule, artifact.kind, artifact.id, kind
                )],
                None => vec![format!(
                    "q{} occ{}: {} has no typed call-contract role ({:?})",
                    query.id, occurrence_index, join_rule, role
                )],
            };
        }
        _ => return Vec::new(),
    };

    let Some(expected_kind) = expected_clause_kind else {
        return vec![format!(
            "q{} occ{}: {} has no typed local-clause role ({:?})",
            query.id, occurrence_index, join_rule, role
        )];
    };

    let mut violations = Vec::new();
    if artifact.kind != expected_kind {
        violations.push(format!(
            "q{} occ{}: {} joined {} artifact {}, expected {}",
            query.id, occurrence_index, join_rule, artifact.kind, artifact.id, expected_kind
        ));
    }
    if artifact.owner != query.fun {
        violations.push(format!(
            "q{} occ{}: local clause artifact {} is owned by {}, expected {}",
            query.id, occurrence_index, artifact.id, artifact.owner, query.fun
        ));
    }
    // The assert-forall hypothesis is the bound variable's assumption; its
    // span is the binder, not the asserted proposition the artifact carries.
    let hypothesis =
        matches!(role, Some(E::AssertForall { point: crate::record::ForallPoint::Hypothesis }));
    match (occurrence.span.as_deref(), artifact.span.as_deref()) {
        _ if hypothesis => {}
        (Some(occurrence_span), Some(artifact_span)) if occurrence_span == artifact_span => {}
        (Some(occurrence_span), Some(artifact_span)) => violations.push(format!(
            "q{} occ{}: artifact {} span {:?} does not match occurrence span {:?}",
            query.id, occurrence_index, artifact.id, artifact_span, occurrence_span
        )),
        (None, _) => violations.push(format!(
            "q{} occ{}: local clause join {} has no occurrence span",
            query.id, occurrence_index, artifact.id
        )),
        (_, None) => violations.push(format!(
            "q{} occ{}: local clause artifact {} has no span",
            query.id, occurrence_index, artifact.id
        )),
    }
    violations
}

pub fn audit(
    r: &CoverageRecord,
    lookup: &dyn Fn(&str) -> Option<&'static crate::rule_schema::Rule>,
) -> Findings {
    let mut v: Vec<String> = Vec::new();
    let mut stats: Vec<(String, String)> = Vec::new();
    let refines: std::collections::BTreeMap<&str, &str> = r
        .refinements
        .iter()
        .map(|(impl_method, trait_method)| (impl_method.as_str(), trait_method.as_str()))
        .collect();

    if r.schema != "verus-proof-coverage/1" {
        v.push(format!("unexpected schema {}", r.schema));
    }
    if r.artifact_version != "0.1" {
        v.push(format!(
            "unsupported or missing artifact_version {:?}; expected \"0.1\"",
            r.artifact_version
        ));
    }
    if !r.record_id.starts_with("pc_r%")
        || r.record_id.len() != 5 + 64
        || !r.record_id[5..].bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        v.push(format!("invalid or missing record_id {:?}", r.record_id));
    }

    // ── source functions (snapshot 1) ────────────────────────────────────
    // One row per function, and the recorded refinement relation must agree
    // with the recorded kinds: every (impl, trait method) pair names an
    // impl whose kind is TraitMethodImpl of that method, and vice versa.
    {
        // `fun` is the raw VIR path, so it is injective by construction; this
        // check is what makes that a checked property of the record rather
        // than a property of the producer. `friendly` is display only and may
        // legitimately be shared (all three `View` impls for `Cow` render
        // `alloc::borrow::Cow::view`), so a shared friendly name is counted,
        // not rejected.
        let mut by_fun: BTreeMap<&str, &crate::record::SourceFunction> = BTreeMap::new();
        let mut friendly_owners: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for sf in &r.source_functions {
            if by_fun.insert(sf.fun.as_str(), sf).is_some() {
                v.push(format!("source function {} recorded twice", sf.fun));
            }
            friendly_owners.entry(sf.friendly.as_str()).or_default().push(sf.fun.as_str());
        }
        let shared_friendly: Vec<(&str, &Vec<&str>)> = friendly_owners
            .iter()
            .filter(|(_, paths)| paths.len() > 1)
            .map(|(friendly, paths)| (*friendly, paths))
            .collect();
        if !shared_friendly.is_empty() {
            stats.push((
                "friendly names shared by several functions".to_string(),
                format!(
                    "{} ({} functions; display only, identities are raw paths)",
                    shared_friendly.len(),
                    shared_friendly.iter().map(|(_, paths)| paths.len()).sum::<usize>()
                ),
            ));
        }
        if !r.source_functions.is_empty() {
            for (impl_method, trait_method) in &r.refinements {
                match by_fun.get(impl_method.as_str()).map(|sf| &sf.kind) {
                    Some(crate::record::FunctionKind::TraitMethodImpl { method, .. })
                        if method == trait_method => {}
                    Some(kind) => v.push(format!(
                        "refinement ({impl_method}, {trait_method}) disagrees with the recorded \
                         kind {kind:?}"
                    )),
                    None => v.push(format!(
                        "refinement ({impl_method}, {trait_method}) names an impl with no source \
                         function row"
                    )),
                }
            }
            for sf in &r.source_functions {
                if let crate::record::FunctionKind::TraitMethodImpl { method, .. } = &sf.kind {
                    if refines.get(sf.fun.as_str()) != Some(&method.as_str()) {
                        v.push(format!(
                            "source function {} implements {} but no refinement row records it",
                            sf.fun, method
                        ));
                    }
                }
            }
            // Every function identity a later table uses must name a row of
            // snapshot 1. Snapshot 1 sees the whole pre-simplified crate,
            // imports included, so an identity that does not resolve is an
            // identity minted somewhere other than `FunX.path` — the failure
            // mode this scheme exists to prevent.
            for function in &r.functions {
                if !by_fun.contains_key(function.fun.as_str()) {
                    v.push(format!(
                        "function record {} has no source function row",
                        function.fun
                    ));
                }
            }
            for query in &r.queries {
                if !by_fun.contains_key(query.fun.as_str()) {
                    v.push(format!("q{}: fun {} has no source function row", query.id, query.fun));
                }
            }
            // Artifact owners and callees may legitimately name a function
            // outside the observed crate graph (an AIR identifier no crate
            // declared resolves to an external artifact), so this is measured
            // rather than rejected.
            let unresolved_owners: BTreeSet<&str> = r
                .artifacts
                .iter()
                .flat_map(|artifact| {
                    std::iter::once(artifact.owner.as_str())
                        .chain(artifact.callee.as_deref())
                })
                .filter(|owner| !by_fun.contains_key(owner))
                .collect();
            if !unresolved_owners.is_empty() {
                stats.push((
                    "artifact owners outside snapshot 1".to_string(),
                    format!("{}", unresolved_owners.len()),
                ));
            }
        }
    }

    // ── label injectivity ───────────────────────────────────────────────
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for q in &r.queries {
        for o in &q.occurrences {
            if let Some(l) = &o.label {
                *seen.entry(l.as_str()).or_insert(0) += 1;
            }
        }
        if let Some(t) = &q.target_label {
            *seen.entry(t.as_str()).or_insert(0) += 1;
        }
    }
    for (l, n) in &seen {
        if *n > 1 {
            v.push(format!("label not injective: {} appears {} times", l, n));
        }
    }
    let ambient_contexts: BTreeMap<&str, BTreeSet<u64>> = r
        .ambients
        .iter()
        .map(|a| (a.label.as_str(), a.solver_contexts.iter().copied().collect()))
        .collect();
    let all_query_labels: BTreeSet<&str> = seen.keys().copied().collect();
    let mut out_of_scope_core_labels = 0u64;

    // ── per-query invariants ────────────────────────────────────────────
    let query_ids: BTreeSet<u64> = r.queries.iter().map(|q| q.id).collect();
    let mut labeled_premises = 0u64;
    let mut labeled_obligations = 0u64;
    let mut unresolved = 0u64;
    let mut placed = 0u64;
    let mut joined = 0u64;
    let ambiguous_placements = 0u64;
    let mut measured = 0u64;
    let mut unsupported_with_evidence = 0u64;
    // Node ids are variant-local. Query.function_variant is the exact
    // observed FuncCheckSst/CFG variant, so placement never falls back to a
    // union over same-name function variants.
    let mut node_index: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut variant_fun: BTreeMap<&str, &str> = BTreeMap::new();
    for f in &r.functions {
        if let Some(previous) = variant_fun.insert(f.variant.as_str(), f.fun.as_str()) {
            if previous != f.fun {
                v.push(format!(
                    "function variant {} is shared by {} and {}",
                    f.variant, previous, f.fun
                ));
            }
        }
        let nodes = node_index.entry(f.variant.as_str()).or_default();
        for node in &f.cfg.nodes {
            nodes.insert(node.id.as_str());
        }
    }
    let artifact_ids: BTreeSet<&str> = r.artifacts.iter().map(|a| a.id.as_str()).collect();
    let artifact_by_id: BTreeMap<&str, &Artifact> =
        r.artifacts.iter().map(|artifact| (artifact.id.as_str(), artifact)).collect();
    if artifact_ids.len() != r.artifacts.len() {
        v.push("artifact ids are not unique".to_string());
    }
    let query_by_id: BTreeMap<u64, &QueryRecord> =
        r.queries.iter().map(|query| (query.id, query)).collect();

    for q in &r.queries {
        let canonical_unproved =
            q.shadow_result.as_deref().is_some_and(|result| result.starts_with("canonical_"));
        if let Some(variant) = q.function_variant.as_deref() {
            match variant_fun.get(variant) {
                Some(fun) if *fun == q.fun => {}
                Some(fun) => v.push(format!(
                    "q{}: function variant {} belongs to {}, not {}",
                    q.id, variant, fun, q.fun
                )),
                None => v.push(format!("q{}: unknown function variant {}", q.id, variant)),
            }
        }
        let own_labels: BTreeSet<&str> =
            q.occurrences.iter().filter_map(|o| o.label.as_deref()).collect();
        let parent_labels: BTreeSet<&str> = q
            .parent
            .and_then(|parent| query_by_id.get(&parent).copied())
            .into_iter()
            .flat_map(|parent| parent.occurrences.iter().filter_map(|o| o.label.as_deref()))
            .collect();
        for label in &q.available {
            if q.target_label.as_deref() == Some(label.as_str())
                || parent_labels.contains(label.as_str())
                || ambient_contexts
                    .get(label.as_str())
                    .is_some_and(|contexts| contexts.contains(&q.solver_context))
            {
                continue;
            }
            v.push(format!(
                "q{}: available label {} does not resolve in its parent query or ambient context",
                q.id, label
            ));
        }
        let available: BTreeSet<&str> = if q.family == QueryFamily::Focused {
            q.available.iter().map(String::as_str).chain(q.target_label.as_deref()).collect()
        } else {
            own_labels
        };

        // role ⟺ carrier polarity; carrier ⟹ placement rules
        for (occurrence_index, o) in q.occurrences.iter().enumerate() {
            let is_assert = o.carrier == Carrier::Assert;
            let is_obligation = o.role == Role::Obligation;
            if is_assert != is_obligation {
                v.push(format!(
                    "q{}: role/carrier polarity violated: role={} carrier={}",
                    q.id, o.role, o.carrier
                ));
            }
            if o.carrier == Carrier::QueryLocalAxiom && o.node.is_some() {
                v.push(format!(
                    "q{}: axiom-carried occurrence has a control placement ({:?})",
                    q.id, o.node
                ));
            }
            if o.origin.kind == OriginKind::Unresolved {
                unresolved += 1;
            }
            match o.role.as_str() {
                "premise" => labeled_premises += 1,
                _ => labeled_obligations += 1,
            }
            // referential integrity of placement and artifact joins
            if let Some(n) = &o.node {
                match q.function_variant.as_deref().and_then(|v| node_index.get(v)) {
                    Some(nodes) if nodes.contains(n.as_str()) => {
                        placed += 1;
                    }
                    Some(_) if !canonical_unproved => v.push(format!(
                        "q{}: placement {} is not a node of variant {:?}",
                        q.id, n, q.function_variant
                    )),
                    None if !canonical_unproved => {
                        v.push(format!("q{}: placement {} has no exact function variant", q.id, n))
                    }
                    _ => {}
                }
            }
            if let Some(a) = &o.artifact {
                if let Some(artifact) = artifact_by_id.get(a.as_str()) {
                    joined += 1;
                    v.extend(audit_typed_artifact_join(q, occurrence_index, o, artifact, &refines));
                } else {
                    v.push(format!("q{}: artifact join {} does not resolve", q.id, a));
                }
            }
        }

        // core ⊆ available ∪ ambients installed in this solver context
        if let Some(core) = &q.core {
            measured += 1;
            if q.shadow_result.as_deref() != Some("valid") {
                unsupported_with_evidence += 1;
                v.push(format!(
                    "q{}: evidence core requires shadow_result=valid, got {:?}",
                    q.id, q.shadow_result
                ));
            }
            if !matches!(
                q.evidence_backend.as_deref(),
                Some("unsat_core" | "proof_enabled_unsat_core")
            ) {
                v.push(format!(
                    "q{}: evidence core has missing or unknown backend {:?}",
                    q.id, q.evidence_backend
                ));
            }
            for l in core {
                if available.contains(l.as_str())
                    || ambient_contexts
                        .get(l.as_str())
                        .is_some_and(|contexts| contexts.contains(&q.solver_context))
                {
                    continue;
                }
                if all_query_labels.contains(l.as_str())
                    || ambient_contexts.contains_key(l.as_str())
                {
                    out_of_scope_core_labels += 1;
                    v.push(format!("q{}: core label {} is outside query scope", q.id, l));
                } else {
                    v.push(format!("q{}: core label {} is not a known label", q.id, l));
                }
            }
        }
        if q.evidence_backend.is_some() && q.core.is_none() {
            v.push(format!("q{}: evidence backend is present without a core", q.id));
        }

        // focused-query structure
        // Exhaustive over QueryFamily.
        match q.family {
            QueryFamily::Focused => {
                match q.parent {
                    Some(p) if query_ids.contains(&p) => {}
                    Some(p) => v.push(format!("q{}: parent q{} does not exist", q.id, p)),
                    None => v.push(format!("q{}: focused query has no parent", q.id)),
                }
                if q.target_label.is_none() {
                    v.push(format!("q{}: focused query has no target label", q.id));
                }
                if q.parent_obligation_label.is_none() {
                    v.push(format!("q{}: focused query has no parent obligation", q.id));
                }
            }
            QueryFamily::Batch => {
                if q.parent.is_some() || q.target_label.is_some() {
                    v.push(format!("q{}: batch query carries focused metadata", q.id));
                }
            }
        }
    }

    // Focused terminal children are total over batch obligations and unique
    // per structural terminal path. One aggregate obligation may decompose
    // into several terminals, but every terminal has exactly one child.
    let mut batch_obligations: BTreeSet<(u64, &str)> = BTreeSet::new();
    for query in r.queries.iter().filter(|query| query.family == QueryFamily::Batch) {
        for occurrence in
            query.occurrences.iter().filter(|occurrence| occurrence.role == Role::Obligation)
        {
            if let Some(label) = occurrence.label.as_deref() {
                batch_obligations.insert((query.id, label));
            } else {
                v.push(format!("q{}: batch obligation has no activation label", query.id));
            }
        }
    }
    let mut focused_by_obligation: BTreeMap<(u64, &str), usize> = BTreeMap::new();
    let mut focused_terminal_paths: BTreeMap<(u64, &str, &str), usize> = BTreeMap::new();
    let mut focused_by_target: BTreeMap<&str, usize> = BTreeMap::new();
    let mut focused_scope_by_obligation: BTreeMap<(u64, &str), BTreeSet<&str>> = BTreeMap::new();
    for query in r.queries.iter().filter(|query| query.family == QueryFamily::Focused) {
        let Some(parent_id) = query.parent else {
            continue;
        };
        let Some(parent_label) = query.parent_obligation_label.as_deref() else {
            continue;
        };
        match query_by_id.get(&parent_id) {
            Some(parent) if parent.family != QueryFamily::Batch => v.push(format!(
                "q{}: focused parent q{} is {}, expected batch",
                query.id, parent_id, parent.family
            )),
            Some(parent) if parent.fun != query.fun => v.push(format!(
                "q{}: focused child function {} differs from parent q{} function {}",
                query.id, query.fun, parent_id, parent.fun
            )),
            _ => {}
        }
        if let Some(parent) = query_by_id.get(&parent_id) {
            if parent.solver_context != query.solver_context {
                v.push(format!(
                    "q{}: focused solver context {} differs from parent q{} context {}",
                    query.id, query.solver_context, parent_id, parent.solver_context
                ));
            }
        }
        if !batch_obligations.contains(&(parent_id, parent_label)) {
            v.push(format!(
                "q{}: parent obligation {} is not an obligation of batch q{}",
                query.id, parent_label, parent_id
            ));
        }
        *focused_by_obligation.entry((parent_id, parent_label)).or_default() += 1;
        match query.terminal_path.as_deref() {
            Some(path) => {
                *focused_terminal_paths.entry((parent_id, parent_label, path)).or_default() += 1;
            }
            None => v.push(format!("q{}: focused query has no terminal path", query.id)),
        }
        if let Some(target) = query.target_label.as_deref() {
            *focused_by_target.entry(target).or_default() += 1;
        }
        let available: BTreeSet<&str> = query
            .available
            .iter()
            .map(String::as_str)
            .filter(|label| Some(*label) != query.target_label.as_deref())
            .collect();
        let scope_key = (parent_id, parent_label);
        if let Some(existing) = focused_scope_by_obligation.get(&scope_key) {
            if existing != &available {
                v.push(format!(
                    "q{}: focused children of batch q{} obligation {} disagree on parent scope",
                    query.id, parent_id, parent_label
                ));
            }
        } else {
            focused_scope_by_obligation.insert(scope_key, available);
        }
    }
    for (parent, label) in &batch_obligations {
        if focused_by_obligation.get(&(*parent, *label)).copied().unwrap_or(0) == 0 {
            v.push(format!(
                "q{}: batch obligation {} has no focused terminal child",
                parent, label
            ));
        }
    }
    for ((parent, label, path), count) in focused_terminal_paths {
        if count != 1 {
            v.push(format!(
                "q{}: batch obligation {} terminal path {:?} has {} focused children",
                parent, label, path, count
            ));
        }
    }

    // focused targets are unique per (parent, target)
    let mut targets: BTreeMap<(Option<u64>, &str), usize> = BTreeMap::new();
    for q in &r.queries {
        if let Some(t) = &q.target_label {
            *targets.entry((q.parent, t.as_str())).or_insert(0) += 1;
        }
    }
    for ((p, t), n) in targets {
        if n > 1 {
            v.push(format!("target {} focused {} times under parent {:?}", t, n, p));
        }
    }

    // ── derivations well-founded; terminals conjoin to their parent ──────
    let all_labels: BTreeSet<&str> = seen.keys().copied().collect();
    let lowering_inputs: BTreeSet<String> = r
        .functions
        .iter()
        .flat_map(|function| {
            function.cfg.nodes.iter().map(|node| format!("{}:{}", function.variant, node.id))
        })
        .collect();
    let mut parent_of_terminal: BTreeMap<&str, &str> = BTreeMap::new();
    let mut split_count_by_target: BTreeMap<&str, usize> = BTreeMap::new();
    for d in &r.derivations {
        // Exhaustive over `Transform`. There is no "unknown transform"
        // violation any more: an unrecognised spelling is now rejected when
        // the record is parsed, so the audit cannot receive one.
        match d.transform {
            Transform::TerminalSplit => {
                if d.inputs.len() != 1 || d.outputs.len() != 1 {
                    v.push(format!(
                        "terminal_split must have exactly one input and one output: {:?} -> {:?}",
                        d.inputs, d.outputs
                    ));
                }
                for i in &d.inputs {
                    if !all_labels.contains(i.as_str()) {
                        v.push(format!("terminal_split input {} is not a known label", i));
                    }
                }
                for o in &d.outputs {
                    *split_count_by_target.entry(o.as_str()).or_default() += 1;
                    if !all_labels.contains(o.as_str()) {
                        v.push(format!("terminal_split output {} is not a known label", o));
                    }
                    if let Some(p) = d.inputs.first() {
                        parent_of_terminal.insert(o.as_str(), p.as_str());
                    }
                }
                if d.inputs.iter().any(|i| d.outputs.contains(i)) {
                    v.push(format!("terminal_split is not well-founded: {:?}", d.inputs));
                }
            }
            Transform::LowerStatement | Transform::LowerAssume => {
                for i in &d.inputs {
                    if !lowering_inputs.contains(i) {
                        v.push(format!("{} input {} is not a known SST/CFG site", d.transform, i));
                    }
                }
                for o in &d.outputs {
                    if !all_labels.contains(o.as_str()) {
                        v.push(format!("{} output {} is not a known label", d.transform, o));
                    }
                }
            }
        }
    }
    // every focused query's target must be recorded as a terminal of its parent
    for q in &r.queries {
        if q.family != QueryFamily::Focused {
            continue;
        }
        let (Some(t), Some(p)) = (&q.target_label, &q.parent_obligation_label) else { continue };
        match parent_of_terminal.get(t.as_str()) {
            Some(recorded) if recorded == &p.as_str() => {}
            Some(recorded) => v.push(format!(
                "terminal {} recorded under {} but focused under {}",
                t, recorded, p
            )),
            None => v.push(format!("terminal {} has no terminal_split derivation", t)),
        }
    }
    for (target, focused_count) in &focused_by_target {
        let split_count = split_count_by_target.get(target).copied().unwrap_or(0);
        if *focused_count != 1 || split_count != 1 {
            v.push(format!(
                "terminal {} has {} focused children and {} terminal_split derivations",
                target, focused_count, split_count
            ));
        }
    }
    for (target, split_count) in split_count_by_target {
        if !focused_by_target.contains_key(target) {
            v.push(format!(
                "terminal_split output {} has no focused query ({} derivations)",
                target, split_count
            ));
        }
    }

    // ── artifact tree integrity ─────────────────────────────────────────
    for a in &r.artifacts {
        if let Some(p) = &a.parent {
            if !artifact_ids.contains(p.as_str()) {
                v.push(format!("artifact {} has dangling parent {}", a.id, p));
            }
        }
        if a.kind.is_clause() && a.parent.is_none() {
            v.push(format!("clause artifact {} has no aggregate parent", a.id));
        }
    }

    // ── cfg integrity ───────────────────────────────────────────────────
    for f in &r.functions {
        let ids: BTreeSet<&str> = f.cfg.nodes.iter().map(|n| n.id.as_str()).collect();
        if !ids.contains(f.cfg.entry.as_str()) {
            v.push(format!("{}: cfg entry {} missing", f.fun, f.cfg.entry));
        }
        if !ids.contains(f.cfg.exit.as_str()) {
            v.push(format!("{}: cfg exit {} missing", f.fun, f.cfg.exit));
        }
        for e in &f.cfg.edges {
            if !ids.contains(e.from.as_str()) || !ids.contains(e.to.as_str()) {
                v.push(format!("{}: edge {} -> {} references unknown node", f.fun, e.from, e.to));
            }
        }
        for n in f.cfg.nodes.iter() {
            if f.cfg.nodes.iter().filter(|m| m.id == n.id).count() > 1 {
                v.push(format!("{}: duplicate cfg node id {}", f.fun, n.id));
            }
        }
        for l in &f.loops {
            for node in [&l.header, &l.body_entry, &l.latch, &l.exit] {
                if !ids.contains(node.as_str()) {
                    v.push(format!("{}: loop references unknown node {}", f.fun, node));
                }
            }
            if !f.cfg.edges.iter().any(|e| e.from == l.latch && e.to == l.header) {
                v.push(format!("{}: loop {} has no back edge", f.fun, l.header));
            }
        }
        for a in &f.sst_assumes {
            if let Some(n) = &a.node {
                if !ids.contains(n.as_str()) {
                    v.push(format!("{}: sst assume node {} not in cfg", f.fun, n));
                }
            }
        }
    }

    // ── join-quality measurements ───────────────────────────────────────
    let mut span_collisions = 0u64;
    let mut span_total = 0u64;
    for f in &r.functions {
        let mut per_span: BTreeMap<&str, usize> = BTreeMap::new();
        for a in &f.sst_assumes {
            *per_span.entry(a.span.as_str()).or_insert(0) += 1;
        }
        for (_, n) in per_span {
            span_total += n as u64;
            if n > 1 {
                span_collisions += n as u64;
            }
        }
    }
    stats.push(("queries".into(), format!("{} ({} measured)", r.queries.len(), measured)));
    stats.push((
        "occurrences".into(),
        format!(
            "{} premises, {} obligations, {} unresolved",
            labeled_premises, labeled_obligations, unresolved
        ),
    ));
    stats.push((
        "placement".into(),
        format!(
            "{} occurrences on cfg nodes, {} artifact joins, {} cfg-variant-ambiguous",
            placed, joined, ambiguous_placements
        ),
    ));
    stats.push((
        "sst span collisions".into(),
        format!(
            "{}/{} assume rows share a span with another ({:.0}%)",
            span_collisions,
            span_total,
            if span_total == 0 { 0.0 } else { 100.0 * span_collisions as f64 / span_total as f64 }
        ),
    ));
    v.extend(audit_recursive_joins(r));
    // Rule-ledger discipline: every attributed row must cite a rule that
    // exists in the ledger and is not Heuristic; every artifact join must
    // cite a join rule.
    let mut rule_usage: std::collections::BTreeMap<String, u64> = std::collections::BTreeMap::new();
    for q in &r.queries {
        if q.family != QueryFamily::Batch {
            continue;
        }
        for (i, o) in q.occurrences.iter().enumerate() {
            if o.origin.kind != OriginKind::Unresolved {
                match &o.rule {
                    None => v.push(format!(
                        "q{} occ{}: attributed ({}/{}) without a cited rule",
                        q.id, i, o.origin.kind, o.origin.detail
                    )),
                    Some(rid) => match lookup(rid) {
                        None => v.push(format!("q{} occ{}: cites unknown rule {}", q.id, i, rid)),
                        Some(rule) if rule.strength == crate::rule_schema::Strength::Heuristic => v
                            .push(format!(
                                "q{} occ{}: heuristic rule {} attributed a row",
                                q.id, i, rid
                            )),
                        Some(_) => {
                            *rule_usage.entry(rid.clone()).or_default() += 1;
                        }
                    },
                }
            }
            if o.artifact.is_some() {
                match &o.join_rule {
                    None => v.push(format!(
                        "q{} occ{}: artifact join ({}) without a cited join rule",
                        q.id,
                        i,
                        o.artifact.as_deref().unwrap_or("")
                    )),
                    Some(rid) if lookup(rid).is_none() => {
                        v.push(format!("q{} occ{}: unknown join rule {}", q.id, i, rid))
                    }
                    Some(rid) => {
                        *rule_usage.entry(format!("join:{}", rid)).or_default() += 1;
                    }
                }
            }
        }
    }
    stats.push((
        "rules cited".into(),
        rule_usage.iter().map(|(k, n)| format!("{}={}", k, n)).collect::<Vec<_>>().join(" "),
    ));
    stats.push(("unsupported-with-evidence".into(), format!("{}", unsupported_with_evidence)));
    stats.push((
        "core labels out of scope".into(),
        format!("{} (expected 0; nonzero means scope computation drift)", out_of_scope_core_labels),
    ));
    Findings { violations: v, stats }
}

/// Per-family provenance-quality table: how many rows each origin family
/// carries, and what fraction have a span, a CFG placement, an artifact
/// join. This is the between-two-stages instrument: it needs no solver
/// evidence at all, so it can sweep arbitrarily many probes cheaply. The
/// `unresolved` rows additionally report their distinct shapes — the
/// worklist for closing the next gap.
pub fn families(r: &CoverageRecord) -> String {
    use std::collections::BTreeMap;
    #[derive(Default)]
    struct Row {
        n: u64,
        with_span: u64,
        with_node: u64,
        with_artifact: u64,
        shapes: BTreeMap<String, u64>,
    }
    let mut prem: BTreeMap<String, Row> = BTreeMap::new();
    let mut obli: BTreeMap<String, Row> = BTreeMap::new();
    for q in &r.queries {
        if q.family != QueryFamily::Batch {
            continue; // focused queries repeat the batch rows
        }
        for o in &q.occurrences {
            let key = format!("{}/{}", o.origin.kind, o.origin.detail);
            // collapse per-callee details into one family
            let key = if key.contains("requires_of:") {
                "source/requires_of_callee".to_string()
            } else if key.contains("ensures_of:") {
                "source/ensures_of_callee".to_string()
            } else {
                key
            };
            let m = if o.role == Role::Premise { &mut prem } else { &mut obli };
            let row = m.entry(key).or_default();
            row.n += 1;
            if o.span.is_some() {
                row.with_span += 1;
            }
            if o.node.is_some() {
                row.with_node += 1;
            }
            if o.artifact.is_some() {
                row.with_artifact += 1;
            }
            if o.origin.kind == OriginKind::Unresolved {
                if let Some(s) = &o.shape {
                    *row.shapes.entry(s.clone()).or_default() += 1;
                }
            }
        }
    }
    let mut out = String::new();
    for (title, m) in [("premises", &prem), ("obligations", &obli)] {
        out.push_str(&format!("  {}:\n", title));
        for (fam, row) in m {
            out.push_str(&format!(
                "    {:<40} {:>4}  span {:>3}  node {:>3}  artifact {:>3}\n",
                fam, row.n, row.with_span, row.with_node, row.with_artifact
            ));
            for (shape, n) in &row.shapes {
                let s = if shape.len() > 90 { &shape[..90] } else { shape };
                out.push_str(&format!("      shape x{}: {}\n", n, s));
            }
        }
    }
    out
}

#[cfg(test)]
mod audit_invariant_tests {
    use super::*;

    static SOURCE_RULE: crate::rule_schema::Rule = crate::rule_schema::Rule {
        id: "test.source",
        producer: "test",
        signals: "test",
        conclusion: "test",
        strength: crate::rule_schema::Strength::Construction,
        constructs: "test",
        negative_probes: "",
    };
    static JOIN_REQUIRES_RULE: crate::rule_schema::Rule = crate::rule_schema::Rule {
        id: "join.requires_index",
        producer: "test",
        signals: "test",
        conclusion: "test",
        strength: crate::rule_schema::Strength::Protocol,
        constructs: "test",
        negative_probes: "",
    };
    static JOIN_AGGREGATE_RULE: crate::rule_schema::Rule = crate::rule_schema::Rule {
        id: "join.contract_aggregate",
        producer: "test",
        signals: "test",
        conclusion: "test",
        strength: crate::rule_schema::Strength::TypedVocabulary,
        constructs: "test",
        negative_probes: "",
    };

    fn test_lookup(id: &str) -> Option<&'static crate::rule_schema::Rule> {
        match id {
            "test.source" => Some(&SOURCE_RULE),
            "join.requires_index" => Some(&JOIN_REQUIRES_RULE),
            "join.contract_aggregate" => Some(&JOIN_AGGREGATE_RULE),
            _ => None,
        }
    }

    /// The solver configuration every query carries. These tests do not vary
    /// it, but the schema has no notion of a query without one.
    fn cfg() -> serde_json::Value {
        serde_json::json!({
            "solver": "z3", "options": [], "rlimit": 0,
            "single_check_query": false, "ignore_unexpected_smt": false,
            "debug": false
        })
    }

    fn record() -> CoverageRecord {
        serde_json::from_value(serde_json::json!({
            "schema": "verus-proof-coverage/1",
            "artifact_version": "0.1",
            "record_id": format!("pc_r%{}", "0".repeat(64)),
            "functions": [],
            "queries": [
                {
                    "id": 0, "family": "batch", "fun": "t::f", "desc": "d", "span": "s",
                    "solver_context": 0, "ambient_batches": 0, "results": [],
                    "solver_config": cfg(),
                    "occurrences": [{
                        "path": "b0", "role": "premise", "carrier": "assume",
                        "origin": {"kind": "unresolved", "detail": "test"},
                        "label": "pc%0%0"
                    }],
                    "core": ["pc%0%0"], "shadow_result": "valid"
                },
                {
                    "id": 1, "family": "batch", "fun": "t::g", "desc": "d", "span": "s",
                    "solver_context": 1, "ambient_batches": 0, "results": [],
                    "solver_config": cfg(),
                    "occurrences": [{
                        "path": "b0", "role": "premise", "carrier": "assume",
                        "origin": {"kind": "unresolved", "detail": "test"},
                        "label": "pc%1%0"
                    }],
                    "core": ["pc%1%0"], "shadow_result": "valid"
                }
            ],
            "ambients": [{"label": "ax", "owner": "t::g", "op": "Broadcast", "solver_contexts": [1]}],
            "artifacts": [],
            "refinements": [],
            "derivations": []
        }))
        .unwrap()
    }

    fn complete_record_value() -> serde_json::Value {
        serde_json::json!({
            "schema": "verus-proof-coverage/1",
            "artifact_version": "0.1",
            "record_id": format!("pc_r%{}", "0".repeat(64)),
            "functions": [],
            "queries": [
                {
                    "id": 0, "family": "batch", "fun": "t::f", "desc": "d", "span": "f.rs:1",
                    "solver_context": 0, "ambient_batches": 0, "results": ["invalid"],
                    "solver_config": cfg(),
                    "shadow_result": "canonical_invalid",
                    "occurrences": [
                        {
                            "path": "b0", "role": "premise", "carrier": "assume",
                            "origin": {"kind": "source", "detail": "requires[0]"},
                            "emission": {"kind": "function_requires", "clause": 0},
                            "span": "f.rs:2", "label": "pc%0%0",
                            "artifact": "t::f#req[0]", "rule": "test.source",
                            "join_rule": "join.requires_index"
                        },
                        {
                            "path": "b1", "role": "obligation", "carrier": "assert",
                            "origin": {"kind": "unresolved", "detail": "test"},
                            "label": "pc%0%1"
                        }
                    ]
                },
                {
                    "id": 1, "family": "focused", "parent": 0, "fun": "t::f",
                    "desc": "d", "span": "f.rs:1",
                    "solver_context": 0, "ambient_batches": 0, "results": [],
                    "solver_config": cfg(),
                    "shadow_result": "canonical_invalid",
                    "parent_obligation_label": "pc%0%1",
                    "target_label": "pc%0%t%1%0",
                    "terminal_path": "",
                    "available": ["pc%0%0", "pc%0%t%1%0"],
                    "occurrences": []
                }
            ],
            "ambients": [],
            "artifacts": [
                {"id": "t::f", "kind": "function", "owner": "t::f"},
                {
                    "id": "t::f#req", "kind": "requires_aggregate",
                    "owner": "t::f", "parent": "t::f"
                },
                {
                    "id": "t::f#req[0]", "kind": "requires_clause",
                    "owner": "t::f", "span": "f.rs:2", "parent": "t::f#req"
                },
                {
                    "id": "t::f#req[1]", "kind": "requires_clause",
                    "owner": "t::f", "span": "f.rs:3", "parent": "t::f#req"
                }
            ],
            "refinements": [],
            "derivations": [{
                "transform": "terminal_split",
                "inputs": ["pc%0%1"],
                "outputs": ["pc%0%t%1%0"]
            }]
        })
    }

    fn complete_record() -> CoverageRecord {
        serde_json::from_value(complete_record_value()).unwrap()
    }

    #[test]
    fn rejects_query_label_from_another_scope() {
        let mut r = record();
        r.queries[0].core = Some(vec!["pc%1%0".into()]);
        let findings = audit(&r, &|_| None);
        assert!(
            findings.violations.iter().any(|v| v.contains("pc%1%0 is outside query scope")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_ambient_from_another_solver_context() {
        let mut r = record();
        r.queries[0].core = Some(vec!["ax".into()]);
        let findings = audit(&r, &|_| None);
        assert!(
            findings.violations.iter().any(|v| v.contains("ax is outside query scope")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn canonical_unsuccessful_batch_keeps_auditable_focused_children() {
        let findings = audit(&complete_record(), &test_lookup);
        assert!(findings.violations.is_empty(), "{:?}", findings.violations);
    }

    /// Two impls of one method for one type render to one friendly name. That
    /// is a property of Verus's display naming, not of its identities, so the
    /// record keeps them apart by raw path and the audit accepts the record.
    #[test]
    fn functions_sharing_a_friendly_name_stay_distinct() {
        let mut value = complete_record_value();
        let source_function = |path: &str, friendly: &str| {
            serde_json::json!({
                "fun": path,
                "friendly": friendly,
                "krate": "t",
                "local": true,
                "mode": "proof",
                "kind": {"kind": "static"},
                "item": "function",
                "module": "t",
                "visibility": {"scope": "public"},
                "body_visibility": {
                    "body": "visible",
                    "visibility": {"scope": "public"}
                },
                "opaqueness": {"opaqueness": "opaque"},
                "has_body": true,
                "external_body": false,
                "broadcast": false
            })
        };
        value["source_functions"] = serde_json::json!([
            source_function("t::impl&%0::method", "t::Type::method"),
            source_function("t::impl&%1::method", "t::Type::method"),
            // The record's queries are owned by `t::f`; every function
            // identity a later table uses must name a snapshot-1 row.
            source_function("t::f", "t::f")
        ]);
        let record: CoverageRecord = serde_json::from_value(value).unwrap();

        let findings = audit(&record, &test_lookup);
        assert!(findings.violations.is_empty(), "{:?}", findings.violations);
        assert!(
            findings.stats.iter().any(|(key, value)| {
                key == "friendly names shared by several functions" && value.starts_with("1 (2 ")
            }),
            "{:?}",
            findings.stats
        );
    }

    /// The raw path is the identity, so a repeated one is a violation.
    #[test]
    fn rejects_a_repeated_function_identity() {
        let mut value = complete_record_value();
        let source_function = |path: &str, friendly: &str| {
            serde_json::json!({
                "fun": path,
                "friendly": friendly,
                "krate": "t",
                "local": true,
                "mode": "proof",
                "kind": {"kind": "static"},
                "item": "function",
                "module": "t",
                "visibility": {"scope": "public"},
                "body_visibility": {
                    "body": "visible",
                    "visibility": {"scope": "public"}
                },
                "opaqueness": {"opaqueness": "opaque"},
                "has_body": true,
                "external_body": false,
                "broadcast": false
            })
        };
        value["source_functions"] = serde_json::json!([
            source_function("t::f", "t::f"),
            source_function("t::f", "t::f")
        ]);
        let record: CoverageRecord = serde_json::from_value(value).unwrap();

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("source function t::f recorded twice")),
            "{:?}",
            findings.violations
        );
    }

    /// A function identity that snapshot 1 never saw was minted somewhere
    /// other than `FunX.path`.
    #[test]
    fn rejects_a_query_function_with_no_source_row() {
        let mut value = complete_record_value();
        value["source_functions"] = serde_json::json!([{
            "fun": "t::other",
            "friendly": "t::other",
            "krate": "t",
            "local": true,
            "mode": "proof",
            "kind": {"kind": "static"},
            "item": "function",
            "module": "t",
            "visibility": {"scope": "public"},
            "body_visibility": {"body": "visible", "visibility": {"scope": "public"}},
            "opaqueness": {"opaqueness": "opaque"},
            "has_body": true,
            "external_body": false,
            "broadcast": false
        }]);
        let record: CoverageRecord = serde_json::from_value(value).unwrap();

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("fun t::f has no source function row")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_a_batch_obligation_whose_focused_child_was_deleted() {
        let mut record = complete_record();
        record.queries.retain(|query| query.family == QueryFamily::Batch);
        record.derivations.clear();

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("batch obligation pc%0%1 has no focused")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_two_focused_children_for_the_same_terminal_path() {
        let mut value = complete_record_value();
        value["queries"].as_array_mut().unwrap().push(serde_json::json!({
            "id": 2, "family": "focused", "parent": 0, "fun": "t::f",
            "desc": "d", "span": "f.rs:1",
            "solver_context": 0, "ambient_batches": 0, "results": [],
            "solver_config": cfg(),
            "shadow_result": "canonical_invalid",
            "parent_obligation_label": "pc%0%1",
            "target_label": "pc%0%t%1%1",
            "terminal_path": "",
            "available": ["pc%0%0", "pc%0%t%1%1"],
            "occurrences": []
        }));
        value["derivations"].as_array_mut().unwrap().push(serde_json::json!({
            "transform": "terminal_split",
            "inputs": ["pc%0%1"],
            "outputs": ["pc%0%t%1%1"]
        }));
        let record = serde_json::from_value(value).unwrap();

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("terminal path \"\" has 2 focused children")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_terminal_siblings_with_different_parent_scopes() {
        let mut value = complete_record_value();
        value["queries"].as_array_mut().unwrap().push(serde_json::json!({
            "id": 2, "family": "focused", "parent": 0, "fun": "t::f",
            "desc": "d", "span": "f.rs:1",
            "solver_context": 0, "ambient_batches": 0, "results": [],
            "solver_config": cfg(),
            "shadow_result": "canonical_invalid",
            "parent_obligation_label": "pc%0%1",
            "target_label": "pc%0%t%1%1",
            "terminal_path": "a1",
            "available": ["pc%0%t%1%1"],
            "occurrences": []
        }));
        value["derivations"].as_array_mut().unwrap().push(serde_json::json!({
            "transform": "terminal_split",
            "inputs": ["pc%0%1"],
            "outputs": ["pc%0%t%1%1"]
        }));
        let record = serde_json::from_value(value).unwrap();

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("disagree on parent scope")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_swapping_a_join_to_another_existing_source_clause() {
        let mut record = complete_record();
        record.queries[0].occurrences[0].artifact = Some("t::f#req[1]".into());

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("does not match occurrence span")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn rejects_mutating_the_span_of_a_joined_source_artifact() {
        let mut record = complete_record();
        let artifact =
            record.artifacts.iter_mut().find(|artifact| artifact.id == "t::f#req[0]").unwrap();
        artifact.span = Some("f.rs:99".into());

        let findings = audit(&record, &test_lookup);
        assert!(
            findings
                .violations
                .iter()
                .any(|violation| violation.contains("does not match occurrence span")),
            "{:?}",
            findings.violations
        );
    }

    #[test]
    fn accepts_an_imported_call_contract_owned_by_the_callee() {
        let mut record = complete_record();
        let occurrence = &mut record.queries[0].occurrences[0];
        occurrence.origin.detail = "ensures_of:external::callee".into();
        occurrence.emission = Some(crate::record::EmissionRole::CallPostcondition {
            callee: "external::callee".into(),
        });
        occurrence.artifact = Some("external::callee#ens".into());
        occurrence.join_rule = Some("join.contract_aggregate".into());
        record.artifacts.push(Artifact {
            id: "external::callee#ens".into(),
            kind: ArtifactKind::EnsuresAggregate,
            owner: "external::callee".into(),
            span: None,
            parent: None,
            callee: None,
            cfg_node: None,
            group: None,
        });

        let findings = audit(&record, &test_lookup);
        assert!(findings.violations.is_empty(), "{:?}", findings.violations);
    }
}

/// Serializable ID-erased context-local view: every emitted context-local
/// field, with query ids and `pc%`/`pc_z%` labels replaced by local
/// ordinals. Comparison is on the serialized struct — adding a record
/// field without extending this view is caught by the table-driven
/// omission tests.
#[derive(serde::Serialize, PartialEq)]
pub struct NormalizedQuery {
    pub ordinal: usize,
    pub family: QueryFamily,
    pub fun: String,
    pub function_variant: Option<String>,
    pub desc: String,
    pub span: String,
    pub ambient_batches: u64,
    pub solver_config: Option<SolverConfigRecord>,
    pub parent: Option<Option<usize>>,
    pub parent_obligation_label: Option<String>,
    pub target_label: Option<String>,
    pub results: Vec<String>,
    pub shadow_result: Option<String>,
    pub evidence_backend: Option<String>,
    pub terminal_path: Option<String>,
    pub occurrences: Vec<NormalizedOccurrence>,
    pub core: Option<Vec<String>>,
    pub available: Vec<String>,
}

#[derive(serde::Serialize, PartialEq)]
pub struct NormalizedOccurrence {
    pub path: String,
    pub role: Role,
    pub carrier: Carrier,
    pub origin_kind: OriginKind,
    pub origin_detail: String,
    pub emission: Option<crate::record::EmissionRole>,
    pub span: Option<String>,
    pub assert_id: Option<String>,
    pub shape: Option<String>,
    // `Occurrence.sig` is deliberately absent. record.rs marks it
    // `#[serde(skip)]`, so no emitted record carries it — verified against the
    // corpus, whose occurrence keys are artifact, assert_id, carrier,
    // emission, join_rule, label, node, origin, path, role, rule, shape, span.
    // Including it here made the interchange surface claim to cover a field
    // that cannot appear in the data.
    pub label: Option<String>,
    pub node: Option<String>,
    pub artifact: Option<String>,
    pub rule: Option<String>,
    pub join_rule: Option<String>,
}

#[derive(serde::Serialize, PartialEq)]
pub struct NormalizedContext {
    pub queries: Vec<NormalizedQuery>,
    pub ambient_memberships: Vec<String>,
    pub derivations: Vec<(Transform, Vec<String>, Vec<String>)>,
}

pub fn normalized_context_views(r: &CoverageRecord) -> BTreeMap<u64, (String, String)> {
    use std::collections::BTreeMap as M;
    let mut ctx_queries: M<u64, Vec<&QueryRecord>> = M::new();
    for q in &r.queries {
        ctx_queries.entry(q.solver_context).or_default().push(q);
    }
    // Contexts that install recorded ambients but issue no queries are still
    // part of the emitted identity space. Their complete emitted content is
    // the ambient-membership set, so it is sufficient both for a stable
    // fingerprint and for interchangeability.
    for ambient in &r.ambients {
        for ctx in &ambient.solver_contexts {
            ctx_queries.entry(*ctx).or_default();
        }
    }
    let mut out = BTreeMap::new();
    for (ctx, qs) in ctx_queries {
        let mut ambient_memberships: Vec<String> = r
            .ambients
            .iter()
            .filter(|a| a.solver_contexts.contains(&ctx))
            .map(|a| a.label.clone())
            .collect();
        ambient_memberships.sort();
        let meta: Vec<_> = qs
            .iter()
            .filter(|q| q.family == QueryFamily::Batch)
            .map(|q| (q.fun.clone(), q.desc.clone(), q.span.clone()))
            .collect();
        let fingerprint = if qs.is_empty() {
            serde_json::to_string(&("queryless", &ambient_memberships)).unwrap()
        } else {
            serde_json::to_string(&meta).unwrap()
        };
        let ord: M<u64, usize> = qs.iter().enumerate().map(|(i, q)| (q.id, i)).collect();
        let rewrite = |s: &str| -> String {
            for pre in ["pc%", "pc_z%"] {
                if let Some(rest) = s.strip_prefix(pre) {
                    if let Some((qid, tail)) = rest.split_once('%') {
                        if let Ok(qid) = qid.parse::<u64>() {
                            if let Some(o) = ord.get(&qid) {
                                return format!("{}q{}%{}", pre, o, tail);
                            }
                        }
                    }
                }
            }
            s.to_string()
        };
        let queries: Vec<NormalizedQuery> = qs
            .iter()
            .map(|q| {
                let mut core =
                    q.core.as_ref().map(|core| core.iter().map(|l| rewrite(l)).collect::<Vec<_>>());
                if let Some(cv) = &mut core {
                    cv.sort();
                }
                let mut available: Vec<String> = q.available.iter().map(|l| rewrite(l)).collect();
                available.sort();
                NormalizedQuery {
                    ordinal: ord[&q.id],
                    family: q.family,
                    fun: q.fun.clone(),
                    function_variant: q.function_variant.clone(),
                    desc: q.desc.clone(),
                    span: q.span.clone(),
                    ambient_batches: q.ambient_batches,
                    solver_config: Some(q.solver_config.clone()),
                    parent: q.parent.map(|p| ord.get(&p).copied()),
                    parent_obligation_label: q.parent_obligation_label.as_deref().map(&rewrite),
                    target_label: q.target_label.as_deref().map(&rewrite),
                    results: q.results.clone(),
                    shadow_result: q.shadow_result.clone(),
                    evidence_backend: q.evidence_backend.clone(),
                    terminal_path: q.terminal_path.clone(),
                    occurrences: q
                        .occurrences
                        .iter()
                        .map(|o| NormalizedOccurrence {
                            path: o.path.clone(),
                            role: o.role,
                            carrier: o.carrier,
                            origin_kind: o.origin.kind,
                            origin_detail: o.origin.detail.clone(),
                            emission: o.emission.clone(),
                            span: o.span.clone(),
                            assert_id: o.assert_id.clone(),
                            shape: o.shape.clone(),
                            label: o.label.as_deref().map(&rewrite),
                            node: o.node.clone(),
                            artifact: o.artifact.clone(),
                            rule: o.rule.clone(),
                            join_rule: o.join_rule.clone(),
                        })
                        .collect(),
                    core,
                    available,
                }
            })
            .collect();
        let mine = |l: &String| {
            l.strip_prefix("pc%")
                .or_else(|| l.strip_prefix("pc_z%"))
                .and_then(|rest| rest.split_once('%'))
                .and_then(|(qid, _)| qid.parse::<u64>().ok())
                .map(|q| ord.contains_key(&q))
                .unwrap_or(false)
        };
        let derivations: Vec<(Transform, Vec<String>, Vec<String>)> = r
            .derivations
            .iter()
            .filter(|d| d.inputs.iter().any(mine) || d.outputs.iter().any(mine))
            .map(|d| {
                (
                    d.transform,
                    d.inputs.iter().map(|l| rewrite(l)).collect(),
                    d.outputs.iter().map(|l| rewrite(l)).collect(),
                )
            })
            .collect();
        let view = NormalizedContext { queries, ambient_memberships, derivations };
        out.insert(ctx, (fingerprint, serde_json::to_string(&view).unwrap()));
    }
    out
}

/// Interchangeability audit over pooled contexts (within and across
/// records): contexts sharing the metadata fingerprint MUST have identical
/// ID-erased views. Returns (groups, violations).
pub fn interchangeability(records: &[(String, CoverageRecord)]) -> (u64, Vec<String>) {
    let mut groups: BTreeMap<String, Vec<(String, u64, String)>> = BTreeMap::new();
    for (name, r) in records {
        for (ctx, (fp, view)) in normalized_context_views(r) {
            groups.entry(fp).or_default().push((name.clone(), ctx, view));
        }
    }
    let mut violations = Vec::new();
    let mut shared = 0u64;
    for (fp, members) in &groups {
        if members.len() < 2 {
            continue;
        }
        shared += 1;
        let first = &members[0];
        for m in &members[1..] {
            if m.2 != first.2 {
                violations.push(format!(
                    "fingerprint {}... shared by {}:ctx{} and {}:ctx{} but ID-erased views differ",
                    &fp[..fp.len().min(60)],
                    first.0,
                    first.1,
                    m.0,
                    m.1
                ));
            }
        }
    }
    (shared, violations)
}

#[cfg(test)]
mod interchange_tests {
    use super::*;

    fn base() -> serde_json::Value {
        serde_json::json!({
            "schema": "verus-proof-coverage/1",
            "artifact_version": "0.1",
            "queries": [{
                "id": 0, "family": "batch", "fun": "t::f", "desc": "d",
                "function_variant": "pc_fv%a",
                "span": "s", "solver_context": 0, "ambient_batches": 2,
                "solver_config": {
                    "solver": "z3",
                    "options": [["air_recommended_options", "true"]],
                    "rlimit": 30000000,
                    "single_check_query": false,
                    "ignore_unexpected_smt": false,
                    "debug": false
                },
                "results": ["valid"], "shadow_result": "valid",
                "evidence_backend": "unsat_core",
                "occurrences": [{
                    "path": "r.b0", "role": "premise", "carrier": "assume",
                    "origin": {"kind": "source", "detail": "x"},
                    "emission": {"kind": "function_ensures"}, "span": "sp", "assert_id": null,
                    "shape": null,
                    "label": "pc%0%0", "node": "r.b0",
                    "artifact": "t::f#a", "rule": "r1", "join_rule": "j1"
                }],
                "core": ["pc%0%0"], "available": ["pc%0%0"],
            }],
            "functions": [], "ambients": [{"label": "ax", "owner": "t::f", "op": "Broadcast", "solver_contexts": [0]}],
            "artifacts": [], "refinements": [],
            "derivations": [{
                "transform": "lower_statement",
                "inputs": ["pc%0%0"], "outputs": ["pc%0%0"]
            }],
        })
    }

    fn check(mutated: serde_json::Value) -> usize {
        let a: CoverageRecord = serde_json::from_value(base()).unwrap();
        let b: CoverageRecord = serde_json::from_value(mutated).unwrap();
        let (_, v) = interchangeability(&[("a".into(), a), ("b".into(), b)]);
        v.len()
    }

    /// Every context-local field, when mutated alone, must cause rejection:
    /// one case per field of the record's query and occurrence rows.
    ///
    /// `Occurrence.sig` is deliberately absent: `record.rs` marks it
    /// `#[serde(skip)]`, so no emitted record carries it and no mutation of it
    /// is observable.
    #[test]
    fn each_field_mutation_is_rejected() {
        let q = "/queries/0";
        let o = "/queries/0/occurrences/0";
        let cases: Vec<(&str, String, serde_json::Value)> = vec![
            ("ambient_batches", format!("{q}/ambient_batches"), serde_json::json!(3)),
            ("function_variant", format!("{q}/function_variant"), serde_json::json!("pc_fv%b")),
            ("solver_config", format!("{q}/solver_config/rlimit"), serde_json::json!(1)),
            ("results", format!("{q}/results/0"), serde_json::json!("invalid")),
            ("shadow_result", format!("{q}/shadow_result"), serde_json::json!("failed")),
            (
                "evidence_backend",
                format!("{q}/evidence_backend"),
                serde_json::json!("proof_enabled_unsat_core"),
            ),
            ("core", format!("{q}/core"), serde_json::json!([])),
            ("available", format!("{q}/available"), serde_json::json!([])),
            ("occ.path", format!("{o}/path"), serde_json::json!("r.b1")),
            ("occ.assert_id", format!("{o}/assert_id"), serde_json::json!("[1]")),
            ("occ.shape", format!("{o}/shape"), serde_json::json!("Eq(_,_)")),
            ("occ.node", format!("{o}/node"), serde_json::json!("r.b9")),
            ("occ.artifact", format!("{o}/artifact"), serde_json::json!("t::f#b")),
            ("occ.rule", format!("{o}/rule"), serde_json::json!("r2")),
            ("occ.join_rule", format!("{o}/join_rule"), serde_json::json!("j2")),
            (
                "occ.emission",
                format!("{o}/emission/kind"),
                serde_json::json!("loop_exit_condition"),
            ),
            ("occ.origin", format!("{o}/origin/detail"), serde_json::json!("y")),
            ("ambients", "/ambients/0/label".to_string(), serde_json::json!("ax2")),
            // A different *valid* variant. The schema now rejects an
            // arbitrary spelling outright, so the interchange check must be
            // exercised with a value a record could actually carry.
            (
                "derivations",
                "/derivations/0/transform".to_string(),
                serde_json::json!("lower_assume"),
            ),
        ];
        for (name, ptr, val) in cases {
            let mut m = base();
            *m.pointer_mut(&ptr).unwrap_or_else(|| panic!("bad pointer {}", ptr)) = val;
            assert_eq!(check(m), 1, "mutation of {} must be rejected", name);
        }
        // sanity: unmutated twin is accepted
        assert_eq!(check(base()), 0, "identical payloads must be accepted");
    }
}

/// ── canonicalization ─────────────────────────────────────────────────────────
///
/// Renumber contexts and queries into fingerprint order so records are
/// byte-deterministic under parallel verification (§6.2 plan). Runtime
/// collision guard: contexts sharing a fingerprint must have identical
/// ID-erased normalized views (the §6.3 comparison); otherwise this
/// function refuses and the caller emits arrival order unchanged.
/// Deterministic identity of one canonical record. The identity is computed
/// with the `record_id` field removed, so it can be embedded in the record
/// without a self-reference.
fn sort_json_keys(value: serde_json::Value) -> serde_json::Value {
    match value {
        serde_json::Value::Object(object) => {
            let sorted = object
                .into_iter()
                .map(|(key, value)| (key, sort_json_keys(value)))
                .collect::<BTreeMap<_, _>>();
            serde_json::Value::Object(sorted.into_iter().collect())
        }
        serde_json::Value::Array(values) => {
            serde_json::Value::Array(values.into_iter().map(sort_json_keys).collect())
        }
        scalar => scalar,
    }
}

pub fn compute_record_id(value: &serde_json::Value) -> Result<String, String> {
    let mut body = value.clone();
    let object =
        body.as_object_mut().ok_or_else(|| "record identity requires a JSON object".to_string())?;
    object.remove("record_id");
    canonicalize(&mut body)?;
    body = sort_json_keys(body);
    let encoded = serde_json::to_vec(&body).map_err(|error| format!("record identity: {error}"))?;
    let digest = Sha256::digest(encoded);
    Ok(format!("pc_r%{}", digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>()))
}

pub fn verify_record_id(value: &serde_json::Value) -> Result<(), String> {
    let recorded = value
        .get("record_id")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "record has no record_id".to_string())?;
    let computed = compute_record_id(value)?;
    if recorded == computed {
        Ok(())
    } else {
        Err(format!("record_id mismatch: recorded {recorded}, computed {computed}"))
    }
}

pub fn canonicalize(value: &mut serde_json::Value) -> Result<(), String> {
    let r: CoverageRecord = serde_json::from_value(value.clone())
        .map_err(|e| format!("canonicalize: unparseable record: {}", e))?;
    // ── guards: all run before any mutation; refusal leaves input unchanged ──
    let views = normalized_context_views(&r);
    let mut by_fp: BTreeMap<&str, Vec<(u64, &str)>> = BTreeMap::new();
    for (ctx, (fp, view)) in &views {
        by_fp.entry(fp.as_str()).or_default().push((*ctx, view.as_str()));
    }
    for (fp, members) in &by_fp {
        for m in &members[1..] {
            if m.1 != members[0].1 {
                return Err(format!(
                    "contexts {} and {} share fingerprint {}... but differ in content",
                    members[0].0,
                    m.0,
                    &fp[..fp.len().min(40)]
                ));
            }
        }
    }
    // ── ranking ──
    let mut ctxs: Vec<(&String, u64)> = views.iter().map(|(ctx, (fp, _))| (fp, *ctx)).collect();
    ctxs.sort();
    let ctx_rank: BTreeMap<u64, u64> =
        ctxs.iter().enumerate().map(|(i, (_, c))| (*c, i as u64)).collect();
    let mut qid_map: BTreeMap<u64, u64> = BTreeMap::new();
    let mut next = 0u64;
    for (_, ctx) in &ctxs {
        for q in r.queries.iter().filter(|q| q.solver_context == *ctx) {
            qid_map.insert(q.id, next);
            next += 1;
        }
    }
    // ── schema-directed rewrite: known identity fields ONLY. A pc%-shaped
    // string in any other field (shape, sig, spans, notes) is content and is
    // preserved verbatim. ──
    let relabel = |v: &mut serde_json::Value| {
        if let Some(s) = v.as_str() {
            if let Some(n) = rewrite_label(s, &qid_map) {
                *v = serde_json::json!(n);
            }
        }
    };
    let relabel_arr = |v: &mut serde_json::Value, sort: bool| {
        if let Some(a) = v.as_array_mut() {
            for e in a.iter_mut() {
                if let Some(s) = e.as_str() {
                    if let Some(n) = rewrite_label(s, &qid_map) {
                        *e = serde_json::json!(n);
                    }
                }
            }
            if sort {
                a.sort_by_key(|e| e.as_str().unwrap_or("").to_string());
            }
        }
    };
    if let Some(qs) = value.get_mut("queries").and_then(|v| v.as_array_mut()) {
        for q in qs.iter_mut() {
            for key in ["id", "parent"] {
                if let Some(x) = q.get_mut(key) {
                    if let Some(old) = x.as_u64() {
                        if let Some(new) = qid_map.get(&old) {
                            *x = serde_json::json!(new);
                        }
                    }
                }
            }
            if let Some(x) = q.get_mut("solver_context") {
                if let Some(old) = x.as_u64() {
                    if let Some(new) = ctx_rank.get(&old) {
                        *x = serde_json::json!(new);
                    }
                }
            }
            for key in ["parent_obligation_label", "target_label"] {
                if let Some(x) = q.get_mut(key) {
                    relabel(x);
                }
            }
            // canonical core/available ordering (post-rewrite sort)
            for key in ["core", "available"] {
                if let Some(x) = q.get_mut(key) {
                    relabel_arr(x, true);
                }
            }
            if let Some(os) = q.get_mut("occurrences").and_then(|v| v.as_array_mut()) {
                for o in os.iter_mut() {
                    if let Some(x) = o.get_mut("label") {
                        relabel(x);
                    }
                }
            }
        }
        qs.sort_by_key(|q| q.get("id").and_then(|i| i.as_u64()).unwrap_or(0));
    }
    // Checked exports name occurrences by label and a query by id, so both
    // are identity fields and both are renumbered. Sorted after rewriting so
    // the relation is byte-stable under parallel verification.
    if let Some(rows) = value.get_mut("checked_exports").and_then(|v| v.as_array_mut()) {
        for row in rows.iter_mut() {
            if let Some(x) = row.get_mut("query") {
                if let Some(old) = x.as_u64() {
                    if let Some(new) = qid_map.get(&old) {
                        *x = serde_json::json!(new);
                    }
                }
            }
            for key in ["check", "export"] {
                if let Some(x) = row.get_mut(key) {
                    relabel(x);
                }
            }
        }
        rows.sort_by_key(|row| {
            (
                row.get("query").and_then(|v| v.as_u64()).unwrap_or(0),
                row.get("check").and_then(|v| v.as_str()).unwrap_or("").to_string(),
                row.get("export").and_then(|v| v.as_str()).unwrap_or("").to_string(),
            )
        });
    }
    if let Some(ams) = value.get_mut("ambients").and_then(|v| v.as_array_mut()) {
        for a in ams.iter_mut() {
            if let Some(scs) = a.get_mut("solver_contexts").and_then(|v| v.as_array_mut()) {
                for e in scs.iter_mut() {
                    if let Some(old) = e.as_u64() {
                        if let Some(new) = ctx_rank.get(&old) {
                            *e = serde_json::json!(new);
                        }
                    }
                }
                scs.sort_by_key(|v| v.as_u64().unwrap_or(0));
            }
        }
    }
    if let Some(ds) = value.get_mut("derivations").and_then(|v| v.as_array_mut()) {
        for d in ds.iter_mut() {
            for key in ["inputs", "outputs"] {
                if let Some(x) = d.get_mut(key) {
                    relabel_arr(x, false);
                }
            }
        }
        ds.sort_by_key(|d| d.to_string());
    }
    if let Some(fs) = value.get_mut("functions").and_then(|v| v.as_array_mut()) {
        fs.sort_by_key(|f| {
            (f.get("fun").and_then(|v| v.as_str()).unwrap_or("").to_string(), f.to_string())
        });
    }
    Ok(())
}

fn rewrite_label(s: &str, qid_map: &BTreeMap<u64, u64>) -> Option<String> {
    for pre in ["pc%", "pc_z%"] {
        if let Some(rest) = s.strip_prefix(pre) {
            if let Some((qid, tail)) = rest.split_once('%') {
                if let Ok(qid) = qid.parse::<u64>() {
                    if let Some(new) = qid_map.get(&qid) {
                        return Some(format!("{}{}%{}", pre, new, tail));
                    }
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod canonicalize_tests {
    use super::*;

    fn base() -> serde_json::Value {
        serde_json::json!({
            "schema": "verus-proof-coverage/1",
            "artifact_version": "0.1",
            "queries": [
                {"id": 7, "family": "batch", "fun": "t::b", "desc": "d", "span": "sB",
                 "solver_context": 3, "ambient_batches": 0, "results": [],
                 "solver_config": {"solver": "z3", "options": [], "rlimit": 0,
                    "single_check_query": false, "ignore_unexpected_smt": false,
                    "debug": false},
                 "occurrences": [{"path": "b0", "role": "premise", "carrier": "assume",
                    "origin": {"kind": "source", "detail": "x"},
                    "label": "pc%7%0", "shape": "Apply(pc%99%bogus)"}],
                 "core": ["pc%7%0", "ax"], "available": ["pc%7%0"]},
                {"id": 2, "family": "batch", "fun": "t::a", "desc": "d", "span": "sA",
                 "solver_context": 1, "ambient_batches": 0, "results": [],
                 "solver_config": {"solver": "z3", "options": [], "rlimit": 0,
                    "single_check_query": false, "ignore_unexpected_smt": false,
                    "debug": false},
                 "occurrences": [], "core": [], "available": []},
                {"id": 9, "family": "focused", "fun": "t::b", "desc": "d", "span": "sB",
                 "solver_context": 3, "ambient_batches": 0, "results": [],
                 "solver_config": {"solver": "z3", "options": [], "rlimit": 0,
                    "single_check_query": false, "ignore_unexpected_smt": false,
                    "debug": false},
                 "parent": 7, "terminal_path": "b0",
                 "parent_obligation_label": "pc%7%0", "target_label": "pc%7%t%0%0",
                 "occurrences": [], "core": ["pc%7%t%0%0"], "available": []}
            ],
            "functions": [],
            "ambients": [{"label": "ax", "owner": "t::b", "op": "Broadcast", "solver_contexts": [3, 1]}],
            "artifacts": [], "refinements": [],
            "derivations": [{
                "transform": "lower_statement",
                "inputs": ["pc%7%0"], "outputs": ["pc%7%t%0%0"]
            }],
        })
    }

    fn canon(mut v: serde_json::Value) -> Result<serde_json::Value, String> {
        canonicalize(&mut v).map(|_| v)
    }

    /// Permuting ids/contexts yields the same canonical bytes.
    #[test]
    fn permutation_invariance() {
        let a = canon(base()).unwrap();
        let mut p = base();
        // swap context ids 3<->1 and query ids 7->4, 2->8, 9->5
        let s = p
            .to_string()
            .replace("\"solver_context\":3", "\"solver_context\":91")
            .replace("\"solver_context\":1", "\"solver_context\":3")
            .replace("\"solver_context\":91", "\"solver_context\":1")
            .replace("pc%7%", "pc%4%")
            .replace("\"id\":7", "\"id\":4")
            .replace("\"parent\":7", "\"parent\":4")
            .replace("\"id\":2", "\"id\":8")
            .replace("\"id\":9", "\"id\":5");
        p = serde_json::from_str(&s).unwrap();
        let b = canon(p).unwrap();
        assert_eq!(a.to_string(), b.to_string());
    }

    /// canonicalize(canonicalize(x)) == canonicalize(x)
    #[test]
    fn idempotence() {
        let once = canon(base()).unwrap();
        let twice = canon(once.clone()).unwrap();
        assert_eq!(once.to_string(), twice.to_string());
    }

    #[test]
    fn record_identity_rejects_payload_mutation() {
        let mut value = base();
        let record_id = compute_record_id(&value).unwrap();
        value
            .as_object_mut()
            .unwrap()
            .insert("record_id".to_string(), serde_json::Value::String(record_id));
        verify_record_id(&value).unwrap();

        *value.pointer_mut("/queries/0/span").unwrap() = serde_json::json!("changed");
        assert!(verify_record_id(&value).is_err());
    }

    /// terminal_path differences are payload: same metadata fingerprint,
    /// different terminal_path must be flagged by interchangeability.
    #[test]
    fn terminal_path_mismatch_rejected() {
        let a: CoverageRecord = serde_json::from_value(base()).unwrap();
        let mut m = base();
        *m.pointer_mut("/queries/2/terminal_path").unwrap() = serde_json::json!("b1");
        let b: CoverageRecord = serde_json::from_value(m).unwrap();
        let (_, v) = interchangeability(&[("a".into(), a), ("b".into(), b)]);
        assert_eq!(v.len(), 1);
    }

    /// Cores are emitted in canonical (sorted) label order.
    #[test]
    fn core_order_normalized() {
        let mut m = base();
        *m.pointer_mut("/queries/0/core").unwrap() = serde_json::json!(["ax", "pc%7%0"]);
        let a = canon(base()).unwrap();
        let b = canon(m).unwrap();
        assert_eq!(a.to_string(), b.to_string());
    }

    /// pc%-shaped strings OUTSIDE identity fields (here: a shape) are
    /// preserved verbatim by schema-directed rewriting.
    #[test]
    fn non_label_pc_strings_preserved() {
        let out = canon(base()).unwrap();
        let shape = out.pointer("/queries/1/occurrences/0/shape").unwrap();
        assert_eq!(shape, &serde_json::json!("Apply(pc%99%bogus)"));
    }

    /// Query-less contexts are ranked by their complete emitted content:
    /// the set of ambient labels installed into them. Renaming such a
    /// context therefore cannot affect canonical bytes.
    #[test]
    fn query_less_context_canonicalized() {
        let mut a = base();
        *a.pointer_mut("/ambients/0/solver_contexts").unwrap() = serde_json::json!([3, 1, 99]);
        let mut b = base();
        *b.pointer_mut("/ambients/0/solver_contexts").unwrap() = serde_json::json!([3, 1, 42]);
        let a = canon(a).unwrap();
        let b = canon(b).unwrap();
        assert_eq!(a.to_string(), b.to_string());
        assert_eq!(canon(a.clone()).unwrap().to_string(), a.to_string());
    }
}

/// Directed SCCs of the *complete recorded* call graph (every call site,
/// guarded or not), restricted to functions present in the record. Each
/// SCC-internal call site is classified guarded (a RecursiveCallRecord
/// exists at its node) or unguarded. This is the *observed* SCC — a
/// projection of the Verus SCC onto recorded functions, not claimed equal.
pub struct ObservedScc {
    pub members: Vec<String>,
    /// (caller, callee, call node, guarded)
    pub internal_calls: Vec<(String, String, String, bool)>,
}

pub fn observed_sccs(r: &CoverageRecord) -> Vec<ObservedScc> {
    let funs: BTreeMap<&str, &FunctionRecord> =
        r.functions.iter().map(|f| (f.fun.as_str(), f)).collect();
    // Tarjan over recorded functions
    let names: Vec<&str> = funs.keys().copied().collect();
    let idx: BTreeMap<&str, usize> = names.iter().enumerate().map(|(i, n)| (*n, i)).collect();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); names.len()];
    for f in &r.functions {
        for (_, _, callee) in &f.call_sites {
            if let Some(callee) = callee {
                if let Some(&j) = idx.get(callee.as_str()) {
                    adj[idx[f.fun.as_str()]].push(j);
                }
            }
        }
    }
    // iterative Tarjan
    let n = names.len();
    let (mut index, mut low, mut on, mut comp) =
        (vec![usize::MAX; n], vec![0usize; n], vec![false; n], vec![usize::MAX; n]);
    let (mut next, mut ncomp) = (0usize, 0usize);
    let mut stack: Vec<usize> = Vec::new();
    for start in 0..n {
        if index[start] != usize::MAX {
            continue;
        }
        let mut call: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&mut (v, ref mut ei)) = call.last_mut() {
            if index[v] == usize::MAX {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on[v] = true;
            }
            if *ei < adj[v].len() {
                let w = adj[v][*ei];
                *ei += 1;
                if index[w] == usize::MAX {
                    call.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                if low[v] == index[v] {
                    while let Some(w) = stack.pop() {
                        on[w] = false;
                        comp[w] = ncomp;
                        if w == v {
                            break;
                        }
                    }
                    ncomp += 1;
                }
                call.pop();
                if let Some(&mut (u, _)) = call.last_mut() {
                    low[u] = low[u].min(low[v]);
                }
            }
        }
    }
    let mut sccs: Vec<ObservedScc> = Vec::new();
    for cid in 0..ncomp {
        let members: Vec<String> =
            (0..n).filter(|&v| comp[v] == cid).map(|v| names[v].to_string()).collect();
        let mset: BTreeSet<&str> = members.iter().map(|s| s.as_str()).collect();
        let mut internal_calls = Vec::new();
        for mname in &members {
            let f = funs[mname.as_str()];
            let guarded_nodes: BTreeSet<&str> =
                f.recursive_calls.iter().map(|rc| rc.call_node.as_str()).collect();
            for (node, _, callee) in &f.call_sites {
                if let Some(callee) = callee {
                    if mset.contains(callee.as_str()) {
                        internal_calls.push((
                            mname.clone(),
                            callee.clone(),
                            node.clone(),
                            guarded_nodes.contains(node.as_str()),
                        ));
                    }
                }
            }
        }
        // an SCC is recursive if multi-member or has a self-edge
        if members.len() > 1 || !internal_calls.is_empty() {
            sccs.push(ObservedScc { members, internal_calls });
        }
    }
    sccs
}

/// Per-RecursiveCallRecord occurrence-join audit: exactly one decreases
/// obligation at guard_node; exactly one ensures_of premise at call_node
/// when the callee has a postcondition (zero otherwise); every requires_of
/// guard of that call at the same call node. Canonically unsuccessful
/// batches are outside successful-proof interpretation and are ignored.
pub fn audit_recursive_joins(r: &CoverageRecord) -> Vec<String> {
    let mut v = Vec::new();
    for f in &r.functions {
        let interpreted_queries: Vec<&QueryRecord> = r
            .queries
            .iter()
            .filter(|q| {
                q.family == QueryFamily::Batch
                    && q.fun == f.fun
                    && !q
                        .shadow_result
                        .as_deref()
                        .is_some_and(|result| result.starts_with("canonical_"))
            })
            .collect();
        if interpreted_queries.is_empty() {
            continue;
        }
        // Observe contract export from the emitted occurrences rather than
        // inferring it from source syntax. A return type invariant may create
        // an ensures predicate without an explicit ensures clause, while a
        // unit-returning function may create no predicate at all.
        let observed_ensures_aggregates: BTreeSet<&str> = interpreted_queries
            .iter()
            .flat_map(|q| q.occurrences.iter())
            .filter(|o| o.role == Role::Premise)
            .filter_map(|o| o.artifact.as_deref())
            .filter(|a| a.ends_with("#ens"))
            .collect();
        for rc in &f.recursive_calls {
            let mut dec = 0;
            let mut ens = 0;
            let mut req_bad = 0;
            for q in &interpreted_queries {
                for o in &q.occurrences {
                    use crate::record::EmissionRole as E;
                    if matches!(o.emission, Some(E::TerminationCheck { .. }))
                        && o.node.as_deref() == Some(rc.guard_node.as_str())
                    {
                        dec += 1;
                    }
                    if o.role == Role::Premise
                        && matches!(o.emission, Some(E::CallPostcondition { .. }))
                        && o.node.as_deref() == Some(rc.call_node.as_str())
                    {
                        ens += 1;
                    }
                    if o.role == Role::Obligation
                        && matches!(
                            o.emission,
                            Some(E::CallPrecondition {
                                callee: Some(_),
                                ..
                            })
                        )
                        && o.span.as_deref() == Some(rc.span.as_str())
                        && o.node.as_deref() != Some(rc.call_node.as_str())
                    {
                        req_bad += 1;
                    }
                }
            }
            if dec != 1 {
                v.push(format!(
                    "{}: recursive call at {} has {} decreases obligations at guard node {}",
                    f.fun, rc.span, dec, rc.guard_node
                ));
            }
            // Exact resolved-method identity and AIR's internal impl name can
            // differ. A matching aggregate proves that one premise is
            // required; otherwise the construction permits either zero
            // (no exported postcondition) or one observed premise. More than
            // one is always an ambiguous join.
            let required_ens = usize::from(
                observed_ensures_aggregates.contains(format!("{}#ens", rc.callee).as_str()),
            );
            if ens < required_ens || ens > 1 {
                v.push(format!(
                    "{}: recursive call at {} has {} ensures_of premises at call node {} (expected {}..=1)",
                    f.fun, rc.span, ens, rc.call_node, required_ens
                ));
            }
            if req_bad != 0 {
                v.push(format!(
                    "{}: {} requires_of guard(s) of the call at {} not at call node {}",
                    f.fun, req_bad, rc.span, rc.call_node
                ));
            }
        }
    }
    v
}
