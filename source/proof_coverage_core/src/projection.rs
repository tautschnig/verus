//! Authoritative source-level projection of focused solver evidence.
//!
//! This module owns the semantics shared by query, function, file, and UI
//! views. Consumers render these values; they must not reconstruct coverage
//! from raw cores independently.

use crate::record::{
    Artifact, ArtifactKind, CoverageRecord, Occurrence, OriginKind, QueryFamily, QueryRecord, Role,
};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CoverageStatus {
    ObservedAll,
    ObservedSome,
    ObservedNone,
    Incomplete,
}

#[derive(Debug, Clone, Serialize)]
pub struct FindingSource {
    pub record_index: usize,
    pub artifact: String,
    pub artifact_kind: ArtifactKind,
    pub owner: String,
    pub span: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FindingTerminal {
    pub terminal_ref: String,
    pub parent_obligation_ref: Option<String>,
    pub artifact: Option<String>,
    pub artifact_kind: Option<ArtifactKind>,
    pub function: String,
    pub span: String,
    pub terminal_path: Option<String>,
    pub record_index: usize,
    pub query_id: u64,
}

/// Query-scope *observations*, not findings. Each row is one (source fact,
/// terminal) pair: the fact was in that query's validated scope and absent
/// from that one witness. `PROOF_COVERAGE.md` §7 is explicit that summing
/// these across queries is meaningless, so they carry observation names and
/// the finding vocabulary of `PROOF_COVERAGE_FINDINGS.md` §2 is reserved for
/// the root-scoped survivors.
#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind")]
pub enum QueryFinding {
    #[serde(rename = "available-not-observed")]
    UncoveredPremise { premise_refs: Vec<String>, source: FindingSource, terminal: FindingTerminal },
    #[serde(rename = "vacuous-terminal")]
    VacuousObligation {
        obligation_ref: String,
        source: Option<FindingSource>,
        terminal: FindingTerminal,
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct PremiseCoverage {
    pub source: FindingSource,
    pub status: CoverageStatus,
    pub functions: Vec<String>,
    pub measured_terminals: Vec<FindingTerminal>,
    pub observed_terminals: Vec<FindingTerminal>,
    pub uncovered_terminals: Vec<FindingTerminal>,
    pub unmeasured_terminals: Vec<FindingTerminal>,
    pub incomplete_terminals: Vec<FindingTerminal>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "kind")]
pub enum AggregateFinding {
    #[serde(rename = "uncovered-premise")]
    UncoveredPremise {
        source: FindingSource,
        functions: Vec<String>,
        terminals: Vec<FindingTerminal>,
    },
    #[serde(rename = "vacuous-obligation")]
    VacuousObligation {
        source: Option<FindingSource>,
        functions: Vec<String>,
        terminals: Vec<FindingTerminal>,
    },
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct ScopeProjection {
    pub premise_coverage: Vec<PremiseCoverage>,
    pub findings: Vec<AggregateFinding>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FunctionProjection {
    pub record_index: usize,
    pub function: String,
    pub premise_coverage: Vec<PremiseCoverage>,
    pub findings: Vec<AggregateFinding>,
}

#[derive(Debug, Clone, Serialize)]
pub struct FileProjection {
    pub record_index: usize,
    pub file: String,
    pub functions: Vec<String>,
    pub premise_coverage: Vec<PremiseCoverage>,
    pub findings: Vec<AggregateFinding>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct FindingProjection {
    pub queries: Vec<QueryFinding>,
    pub functions: Vec<FunctionProjection>,
    pub files: Vec<FileProjection>,
}

// ── self-measurement: what this analysis does not cover ─────────────────────
//
// Two independently obtained populations are compared by set difference over
// audited relations only:
//
//   Declared(a)  a source construct inventoried in the record's artifact
//                table, independently of whether any query observed it;
//   Measured(a)  some occurrence carries an audited projection onto a.
//
// `Declared \ Measured` is an instrumentation gap: source the analysis cannot
// speak about. The mirror population is source-like evidence that reached the
// solver without a source identity. Neither is a proof finding: they measure
// the analysis, not the proof, and must be reported separately so a coverage
// claim always carries its own denominator.

/// Source-construct artifact kinds that name one user-written clause.
/// Aggregates, call sites, and functions are containers, not clauses.
const CLAUSE_KINDS: &[&str] = &[
    "requires_clause",
    "ensures_clause",
    "loop_invariant_clause",
    "assertion",
    "lemma_requires_clause",
    "lemma_ensures_clause",
];

#[derive(Debug, Clone, Serialize)]
pub struct DeclaredClause {
    pub record_index: usize,
    pub artifact: String,
    pub artifact_kind: ArtifactKind,
    pub owner: String,
    pub span: Option<String>,
    /// `local` when the owner has an observed query or function variant in
    /// this record; `imported` otherwise. An imported clause is expected to
    /// be unmeasured: a callee contract enters a caller as one aggregate.
    pub locality: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub struct UnprojectedEvidence {
    pub record_index: usize,
    pub function: String,
    pub origin_detail: String,
    pub phase: Option<String>,
    pub occurrences: usize,
    pub sample_span: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct AnalysisCoverage {
    pub declared_local: usize,
    pub measured_local: usize,
    pub declared_imported: usize,
    pub measured_imported: usize,
    /// Declared source clauses with no audited projection (local first).
    pub instrumentation_gaps: Vec<DeclaredClause>,
    /// Source-like occurrences that reached a query without a source identity.
    pub unprojected_evidence: Vec<UnprojectedEvidence>,
    /// Occurrences whose provenance rules all failed, by reason bucket.
    pub unresolved_residue: Vec<(String, usize)>,
}

/// Measure this analysis against the source it claims to cover.
pub fn analysis_coverage(records: &[CoverageRecord]) -> AnalysisCoverage {
    let mut out = AnalysisCoverage::default();
    let mut unprojected: BTreeMap<
        (usize, String, String, Option<String>),
        (usize, Option<String>),
    > = BTreeMap::new();
    let mut unresolved: BTreeMap<String, usize> = BTreeMap::new();

    for (record_index, record) in records.iter().enumerate() {
        let observed_owners: BTreeSet<&str> = record
            .queries
            .iter()
            .map(|query| query.fun.as_str())
            .chain(record.functions.iter().map(|function| function.fun.as_str()))
            .collect();
        let mut measured: BTreeSet<&str> = BTreeSet::new();
        for query in &record.queries {
            for occurrence in &query.occurrences {
                match occurrence.artifact.as_deref() {
                    Some(artifact) => {
                        measured.insert(artifact);
                    }
                    None if occurrence.origin.kind == OriginKind::Source => {
                        let key = (
                            record_index,
                            query.fun.clone(),
                            occurrence.origin.detail.clone(),
                            occurrence.phase(),
                        );
                        let entry = unprojected.entry(key).or_insert((0, occurrence.span.clone()));
                        entry.0 += 1;
                    }
                    None => {}
                }
                if occurrence.origin.kind == OriginKind::Unresolved {
                    *unresolved.entry(occurrence.origin.detail.clone()).or_default() += 1;
                }
            }
        }

        for artifact in &record.artifacts {
            if !CLAUSE_KINDS.contains(&artifact.kind.as_str()) {
                continue;
            }
            let local = observed_owners.contains(artifact.owner.as_str());
            let is_measured = measured.contains(artifact.id.as_str());
            match (local, is_measured) {
                (true, true) => out.measured_local += 1,
                (true, false) => out.declared_local += 1,
                (false, true) => out.measured_imported += 1,
                (false, false) => out.declared_imported += 1,
            }
            if !is_measured {
                out.instrumentation_gaps.push(DeclaredClause {
                    record_index,
                    artifact: artifact.id.clone(),
                    artifact_kind: artifact.kind.clone(),
                    owner: artifact.owner.clone(),
                    span: artifact.span.clone(),
                    locality: if local { "local" } else { "imported" },
                });
            }
        }
    }
    // Declared counts above tallied only the unmeasured ones; make them totals.
    out.declared_local += out.measured_local;
    out.declared_imported += out.measured_imported;

    out.instrumentation_gaps.sort_by(|left, right| {
        (left.locality, &left.owner, &left.artifact).cmp(&(
            right.locality,
            &right.owner,
            &right.artifact,
        ))
    });
    out.unprojected_evidence = unprojected
        .into_iter()
        .map(|((record_index, function, origin_detail, phase), (occurrences, sample_span))| {
            UnprojectedEvidence {
                record_index,
                function,
                origin_detail,
                phase,
                occurrences,
                sample_span,
            }
        })
        .collect();
    out.unprojected_evidence.sort_by(|left, right| {
        right.occurrences.cmp(&left.occurrences).then_with(|| {
            (&left.function, &left.origin_detail).cmp(&(&right.function, &right.origin_detail))
        })
    });
    out.unresolved_residue = unresolved.into_iter().collect();
    out
}

#[derive(Clone)]
struct PremisePair {
    premise_refs: BTreeSet<String>,
    source: FindingSource,
    terminal: FindingTerminal,
    measured: bool,
    observed: bool,
    attribution_complete: bool,
}

#[derive(Clone)]
struct VacuousTerminal {
    obligation_ref: String,
    source: Option<FindingSource>,
    terminal: FindingTerminal,
}

fn namespaced(record_count: usize, record_index: usize, value: &str) -> String {
    if record_count > 1 { format!("r{record_index}%{value}") } else { value.to_string() }
}

fn measured_evidence(query: &QueryRecord) -> Option<BTreeSet<&str>> {
    if query.shadow_result.as_deref() != Some("valid") {
        return None;
    }
    match query.evidence_backend.as_deref() {
        Some("unsat_core" | "proof_enabled_unsat_core") => {}
        _ => return None,
    }
    query.core.as_ref().map(|core| core.iter().map(String::as_str).collect())
}

fn source_for(
    record_index: usize,
    artifacts: &BTreeMap<&str, &Artifact>,
    artifact_id: &str,
) -> Option<FindingSource> {
    let artifact = artifacts.get(artifact_id)?;
    Some(FindingSource {
        record_index,
        artifact: artifact.id.clone(),
        artifact_kind: artifact.kind.clone(),
        owner: artifact.owner.clone(),
        span: artifact.span.clone(),
    })
}

fn terminal_for(
    record_count: usize,
    record_index: usize,
    query: &QueryRecord,
    occurrences: &BTreeMap<&str, Vec<&Occurrence>>,
    artifacts: &BTreeMap<&str, &Artifact>,
) -> FindingTerminal {
    let obligation = query
        .parent_obligation_label
        .as_deref()
        .and_then(|label| occurrences.get(label))
        .and_then(|values| values.as_slice().first().copied())
        .filter(|occurrence| occurrence.role == Role::Obligation);
    let artifact = obligation.and_then(|occurrence| occurrence.artifact.as_deref());
    FindingTerminal {
        terminal_ref: namespaced(
            record_count,
            record_index,
            query.target_label.as_deref().unwrap_or(""),
        ),
        parent_obligation_ref: query
            .parent_obligation_label
            .as_deref()
            .map(|label| namespaced(record_count, record_index, label)),
        artifact: artifact.map(str::to_string),
        artifact_kind: artifact
            .and_then(|artifact| artifacts.get(artifact))
            .map(|artifact| artifact.kind.clone()),
        function: query.fun.clone(),
        span: query.span.clone(),
        terminal_path: query.terminal_path.clone(),
        record_index,
        query_id: query.id,
    }
}

fn span_file(span: &str) -> Option<String> {
    let end = span.rfind(".rs:")? + 3;
    Some(span[..end].to_string())
}

fn aggregate_pairs(groups: BTreeMap<(usize, String), Vec<PremisePair>>) -> Vec<PremiseCoverage> {
    groups
        .into_values()
        .filter_map(|mut pairs| {
            pairs.sort_by(|left, right| {
                left.terminal.terminal_ref.cmp(&right.terminal.terminal_ref)
            });
            let source = pairs.first()?.source.clone();
            let functions = pairs
                .iter()
                .map(|pair| pair.terminal.function.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let measured_terminals = pairs
                .iter()
                .filter(|pair| pair.measured)
                .map(|pair| pair.terminal.clone())
                .collect::<Vec<_>>();
            let observed_terminals = pairs
                .iter()
                .filter(|pair| pair.measured && pair.attribution_complete && pair.observed)
                .map(|pair| pair.terminal.clone())
                .collect::<Vec<_>>();
            let uncovered_terminals = pairs
                .iter()
                .filter(|pair| pair.measured && pair.attribution_complete && !pair.observed)
                .map(|pair| pair.terminal.clone())
                .collect::<Vec<_>>();
            let unmeasured_terminals = pairs
                .iter()
                .filter(|pair| !pair.measured)
                .map(|pair| pair.terminal.clone())
                .collect::<Vec<_>>();
            let incomplete_terminals = pairs
                .iter()
                .filter(|pair| pair.measured && !pair.attribution_complete)
                .map(|pair| pair.terminal.clone())
                .collect::<Vec<_>>();
            let status = if !unmeasured_terminals.is_empty() || !incomplete_terminals.is_empty() {
                CoverageStatus::Incomplete
            } else if uncovered_terminals.is_empty() {
                CoverageStatus::ObservedAll
            } else if observed_terminals.is_empty() {
                CoverageStatus::ObservedNone
            } else {
                CoverageStatus::ObservedSome
            };
            Some(PremiseCoverage {
                source,
                status,
                functions,
                measured_terminals,
                observed_terminals,
                uncovered_terminals,
                unmeasured_terminals,
                incomplete_terminals,
            })
        })
        .collect()
}

fn scope_projection(
    pairs: impl IntoIterator<Item = PremisePair>,
    vacuous: impl IntoIterator<Item = VacuousTerminal>,
) -> ScopeProjection {
    let mut pair_groups: BTreeMap<(usize, String), Vec<PremisePair>> = BTreeMap::new();
    for pair in pairs {
        pair_groups
            .entry((pair.source.record_index, pair.source.artifact.clone()))
            .or_default()
            .push(pair);
    }
    let premise_coverage = aggregate_pairs(pair_groups);
    let mut findings = premise_coverage
        .iter()
        .filter(|coverage| coverage.status == CoverageStatus::ObservedNone)
        .map(|coverage| AggregateFinding::UncoveredPremise {
            source: coverage.source.clone(),
            functions: coverage.functions.clone(),
            terminals: coverage.uncovered_terminals.clone(),
        })
        .collect::<Vec<_>>();

    let mut vacuous_groups: BTreeMap<(usize, String), Vec<VacuousTerminal>> = BTreeMap::new();
    for terminal in vacuous {
        let key = terminal
            .source
            .as_ref()
            .map(|source| source.artifact.clone())
            .unwrap_or_else(|| terminal.terminal.terminal_ref.clone());
        vacuous_groups.entry((terminal.terminal.record_index, key)).or_default().push(terminal);
    }
    for mut terminals in vacuous_groups.into_values() {
        terminals
            .sort_by(|left, right| left.terminal.terminal_ref.cmp(&right.terminal.terminal_ref));
        let Some(first) = terminals.first() else { continue };
        findings.push(AggregateFinding::VacuousObligation {
            source: first.source.clone(),
            functions: terminals
                .iter()
                .map(|terminal| terminal.terminal.function.clone())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            terminals: terminals.into_iter().map(|terminal| terminal.terminal).collect(),
        });
    }
    findings.sort_by_key(|finding| match finding {
        AggregateFinding::UncoveredPremise { source, .. } => {
            (source.record_index, 0, source.artifact.clone())
        }
        AggregateFinding::VacuousObligation { source, terminals, .. } => (
            terminals.first().map(|terminal| terminal.record_index).unwrap_or_default(),
            1,
            source
                .as_ref()
                .map(|source| source.artifact.clone())
                .or_else(|| terminals.first().map(|terminal| terminal.terminal_ref.clone()))
                .unwrap_or_default(),
        ),
    });
    ScopeProjection { premise_coverage, findings }
}

/// Project focused-query evidence to source artifacts.
///
/// Absence findings are emitted only when the shadow result is valid, the
/// evidence backend is known, the core is present, and every source-like
/// available premise in that focused query is attributed. Any unresolved or
/// unjoined source-like row makes the affected terminal incomplete.
pub fn project(records: &[CoverageRecord]) -> FindingProjection {
    let record_count = records.len();
    let mut pairs: BTreeMap<(usize, String, String), PremisePair> = BTreeMap::new();
    let mut vacuous: BTreeMap<String, VacuousTerminal> = BTreeMap::new();
    let mut file_functions: BTreeMap<(usize, String), BTreeSet<String>> = BTreeMap::new();

    for (record_index, record) in records.iter().enumerate() {
        let artifacts: BTreeMap<_, _> =
            record.artifacts.iter().map(|artifact| (artifact.id.as_str(), artifact)).collect();
        let mut occurrences: BTreeMap<&str, Vec<&Occurrence>> = BTreeMap::new();
        for occurrence in record.queries.iter().flat_map(|query| &query.occurrences) {
            if let Some(label) = occurrence.label.as_deref() {
                occurrences.entry(label).or_default().push(occurrence);
            }
        }

        for query in record.queries.iter().filter(|query| query.family == QueryFamily::Focused) {
            let Some(target) = query.target_label.as_deref() else { continue };
            if let Some(file) = span_file(&query.span) {
                file_functions.entry((record_index, file)).or_default().insert(query.fun.clone());
            }
            let terminal =
                terminal_for(record_count, record_index, query, &occurrences, &artifacts);
            let evidence = measured_evidence(query);

            let mut candidates = Vec::new();
            let mut attribution_complete = true;
            for premise_ref in &query.available {
                if premise_ref == target {
                    continue;
                }
                let Some(values) = occurrences.get(premise_ref.as_str()) else {
                    attribution_complete = false;
                    continue;
                };
                if values.len() != 1 {
                    attribution_complete = false;
                }
                for occurrence in values {
                    if occurrence.role != Role::Premise {
                        continue;
                    }
                    match occurrence.artifact.as_deref() {
                        Some(artifact_id) => {
                            if let Some(source) = source_for(record_index, &artifacts, artifact_id)
                            {
                                candidates.push((
                                    artifact_id.to_string(),
                                    namespaced(record_count, record_index, premise_ref),
                                    source,
                                    evidence
                                        .as_ref()
                                        .is_some_and(|core| core.contains(premise_ref.as_str())),
                                ));
                            } else {
                                attribution_complete = false;
                            }
                        }
                        None if matches!(
                            occurrence.origin.kind.as_str(),
                            "source" | "unresolved"
                        ) =>
                        {
                            attribution_complete = false;
                        }
                        None => {}
                    }
                }
            }

            for (artifact_id, premise_ref, source, observed) in candidates {
                let key = (record_index, artifact_id, terminal.terminal_ref.clone());
                let pair = pairs.entry(key).or_insert_with(|| PremisePair {
                    premise_refs: BTreeSet::new(),
                    source,
                    terminal: terminal.clone(),
                    measured: evidence.is_some(),
                    observed: false,
                    attribution_complete,
                });
                pair.premise_refs.insert(premise_ref);
                pair.measured |= evidence.is_some();
                pair.observed |= observed;
                pair.attribution_complete &= attribution_complete;
            }

            if evidence.as_ref().is_some_and(|core| !core.contains(target)) {
                let source = terminal
                    .artifact
                    .as_deref()
                    .and_then(|artifact| source_for(record_index, &artifacts, artifact));
                let obligation_ref = query
                    .parent_obligation_label
                    .as_deref()
                    .map(|label| namespaced(record_count, record_index, label))
                    .unwrap_or_else(|| namespaced(record_count, record_index, target));
                vacuous.entry(terminal.terminal_ref.clone()).or_insert(VacuousTerminal {
                    obligation_ref,
                    source,
                    terminal,
                });
            }
        }
    }

    let mut query_findings = pairs
        .values()
        .filter(|pair| pair.measured && pair.attribution_complete && !pair.observed)
        .map(|pair| QueryFinding::UncoveredPremise {
            premise_refs: pair.premise_refs.iter().cloned().collect(),
            source: pair.source.clone(),
            terminal: pair.terminal.clone(),
        })
        .chain(vacuous.values().map(|terminal| QueryFinding::VacuousObligation {
            obligation_ref: terminal.obligation_ref.clone(),
            source: terminal.source.clone(),
            terminal: terminal.terminal.clone(),
        }))
        .collect::<Vec<_>>();
    query_findings.sort_by_key(|finding| match finding {
        QueryFinding::UncoveredPremise { source, terminal, .. } => {
            (terminal.record_index, terminal.terminal_ref.clone(), 0, source.artifact.clone())
        }
        QueryFinding::VacuousObligation { terminal, source, .. } => (
            terminal.record_index,
            terminal.terminal_ref.clone(),
            1,
            source.as_ref().map(|source| source.artifact.clone()).unwrap_or_default(),
        ),
    });

    let mut function_pairs: BTreeMap<(usize, String), Vec<PremisePair>> = BTreeMap::new();
    for pair in pairs.values() {
        function_pairs
            .entry((pair.terminal.record_index, pair.terminal.function.clone()))
            .or_default()
            .push(pair.clone());
    }
    let mut function_vacuous: BTreeMap<(usize, String), Vec<VacuousTerminal>> = BTreeMap::new();
    for terminal in vacuous.values() {
        function_vacuous
            .entry((terminal.terminal.record_index, terminal.terminal.function.clone()))
            .or_default()
            .push(terminal.clone());
    }
    let function_keys =
        function_pairs.keys().chain(function_vacuous.keys()).cloned().collect::<BTreeSet<_>>();
    let functions = function_keys
        .into_iter()
        .map(|(record_index, function)| {
            let projection = scope_projection(
                function_pairs.remove(&(record_index, function.clone())).unwrap_or_default(),
                function_vacuous.remove(&(record_index, function.clone())).unwrap_or_default(),
            );
            FunctionProjection {
                record_index,
                function,
                premise_coverage: projection.premise_coverage,
                findings: projection.findings,
            }
        })
        .collect();

    let mut file_pairs: BTreeMap<(usize, String), Vec<PremisePair>> = BTreeMap::new();
    for pair in pairs.values() {
        if let Some(file) = pair.source.span.as_deref().and_then(span_file) {
            file_functions
                .entry((pair.source.record_index, file.clone()))
                .or_default()
                .insert(pair.terminal.function.clone());
            file_pairs.entry((pair.source.record_index, file)).or_default().push(pair.clone());
        }
    }
    let mut file_vacuous: BTreeMap<(usize, String), Vec<VacuousTerminal>> = BTreeMap::new();
    for terminal in vacuous.values() {
        if let Some(file) =
            terminal.source.as_ref().and_then(|source| source.span.as_deref()).and_then(span_file)
        {
            file_functions
                .entry((terminal.terminal.record_index, file.clone()))
                .or_default()
                .insert(terminal.terminal.function.clone());
            file_vacuous
                .entry((terminal.terminal.record_index, file))
                .or_default()
                .push(terminal.clone());
        }
    }
    let files = file_functions
        .into_iter()
        .map(|((record_index, file), functions)| {
            let projection = scope_projection(
                file_pairs.remove(&(record_index, file.clone())).unwrap_or_default(),
                file_vacuous.remove(&(record_index, file.clone())).unwrap_or_default(),
            );
            FileProjection {
                record_index,
                file,
                functions: functions.into_iter().collect(),
                premise_coverage: projection.premise_coverage,
                findings: projection.findings,
            }
        })
        .collect();

    FindingProjection { queries: query_findings, functions, files }
}
