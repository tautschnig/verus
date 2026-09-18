//! L3: the licensing rules.
//!
//! Everything in this module is a claim about what proof dependency means:
//! which checked obligations license which exported assumptions. A reviewer
//! can reject any rule here without a single row of [`crate::facts`]
//! changing. Each rule is one paragraph; together they are the analyzer's
//! definition of a verification argument beyond the solver's own
//! `SupportedBy` evidence.
//!
//! Rules 1–5 materialize static `CertifiedBy` hyperarcs. Rule 6 is not a
//! static arc: calls are call-local relations ([`DemandCall`]) that
//! [`crate::analysis`] consumes while slicing. The rules quantify over typed
//! [`EmissionRole`] values and recorded identities — never over spans,
//! statement order, formula equality, or rendered strings.
//!
//! The checked-export shape (`PROOF_COVERAGE.md` §5) is the common form:
//! hypotheses `H`, goal obligation `G`, exported assumption `E`, with
//! `CertifiedBy(H ∪ {G}) → E`. Rules 1–4 are instances of it; rule 5 is the
//! callee side of a contract; rule 6 carries the caller side and the induction
//! principle.

use std::collections::{BTreeMap, BTreeSet};

use crate::analysis::{Arc, ArcKind};
use crate::facts::{Facts, RecordFacts};
use crate::record::{
    AssertQueryPoint, AssertionPoint, ContractSection, EmissionRole, ForallPoint,
    LoopInvariantGroup, LoopPoint, OriginKind, Role, TerminationPoint,
};

/// The licensing rules, in application order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LicensingRule {
    /// 1. Loop protocol. For one invariant clause: the establish check
    ///    licenses the body-entry hypothesis; the establish check together
    ///    with the maintain and transfer checks licenses the exit export. The
    ///    tails follow the clause's declared group: `invariant_except_break`
    ///    exports nothing at exit; `loop_ensures` needs no establish check.
    LoopProtocol,
    /// 2. Assert-query protocol (`assert ... by(nonlinear_arith |
    ///    bit_vector)`). The outer requires check licenses the inner
    ///    hypothesis; the inner goal licenses the outer exported conclusion.
    AssertQueryProtocol,
    /// 3. Assert protocol. A user assertion's discharged check licenses the
    ///    proposition assumed immediately after it.
    AssertProtocol,
    /// 4. Assert-forall protocol. The proved body goal licenses the exported
    ///    quantified conclusion.
    AssertForallProtocol,
    /// 5. Contract, callee side. A function's ensures checks license its
    ///    ensures clause artifacts.
    ContractCallee,
    /// 6. Checked exports the producer paired construction-exactly, from
    ///    `CoverageRecord.checked_exports`. Rules 1–5 pair their two halves
    ///    through a shared source artifact; this one exists for the
    ///    constructs that have no artifact to share — a generated overflow or
    ///    pattern-match check, an invariant block — where the encoding still
    ///    admits the assumption only after discharging the check.
    CheckedExport,
    /// 7. Calls, as call-local relations rather than static arcs. An ordinary
    ///    call is based on the callee's ensures aggregate; a recursive call on
    ///    *that call's* own decrease guard, so the hypothesis is never licensed
    ///    by the function's own ensures check. See [`DemandCall`] for what the
    ///    tail does and does not contain.
    ContractCaller,
}

impl LicensingRule {
    pub const ALL: &'static [LicensingRule] = &[
        LicensingRule::LoopProtocol,
        LicensingRule::AssertQueryProtocol,
        LicensingRule::AssertProtocol,
        LicensingRule::AssertForallProtocol,
        LicensingRule::ContractCallee,
        LicensingRule::CheckedExport,
        LicensingRule::ContractCaller,
    ];

    pub fn name(self) -> &'static str {
        match self {
            LicensingRule::LoopProtocol => "loop protocol",
            LicensingRule::AssertQueryProtocol => "assert-query protocol",
            LicensingRule::AssertProtocol => "assert protocol",
            LicensingRule::AssertForallProtocol => "assert-forall protocol",
            LicensingRule::ContractCallee => "contract (callee side)",
            LicensingRule::CheckedExport => "recorded checked exports",
            LicensingRule::ContractCaller => "calls (ordinary and recursive)",
        }
    }

    /// The arcs this rule licenses over one record's facts. Rule 6 produces no
    /// static arc; its relations are built by [`demand_calls`].
    pub fn arcs(self, rf: &RecordFacts<'_>, f: &Facts<'_>) -> Vec<Arc> {
        match self {
            LicensingRule::LoopProtocol => loop_protocol(rf, f),
            LicensingRule::AssertQueryProtocol => assert_query_protocol(rf),
            LicensingRule::AssertProtocol => assert_protocol(rf),
            LicensingRule::AssertForallProtocol => assert_forall_protocol(rf),
            LicensingRule::ContractCallee => contract_callee(rf),
            LicensingRule::CheckedExport => checked_exports(rf),
            LicensingRule::ContractCaller => Vec::new(),
        }
    }
}

fn certified(tail: impl IntoIterator<Item = String>, head: String, why: String) -> Arc {
    Arc {
        tail: tail.into_iter().collect(),
        head: BTreeSet::from([head]),
        kind: ArcKind::CertifiedBy,
        query: None,
        why,
    }
}

fn loop_protocol(rf: &RecordFacts<'_>, f: &Facts<'_>) -> Vec<Arc> {
    let at = |p: LoopPoint| EmissionRole::LoopInvariant { point: p };
    let mut arcs = Vec::new();
    for a in rf.by_artifact.keys() {
        // Licensing derived from the clause's declared group (vir::sst::LoopInv
        // flags) rather than one fixed shape:
        //
        //   invariant_except_break  entry ⊢ body hypothesis; no exit export
        //   invariant               entry ⊢ body hypothesis;
        //                           entry + latch/transfer ⊢ exit export
        //   loop_ensures            latch/transfer ⊢ exit export (no entry)
        //
        // Transfer rows are *obligations* (invariants checked at a labeled
        // break/continue) and belong in the licensing tail.
        let entry = rf.at(a, &at(LoopPoint::Establish));
        let mut step: Vec<String> = rf.at(a, &at(LoopPoint::Maintain));
        step.extend(rf.at(a, &at(LoopPoint::Transfer)));
        let header = rf.at(a, &at(LoopPoint::BodyEntry));
        let exit = rf.at(a, &at(LoopPoint::Exit));
        let group = f.artifact_group.get(a).copied();
        let exports_at_exit = !matches!(group, Some(LoopInvariantGroup::InvariantExceptBreak));
        let requires_entry = !matches!(group, Some(LoopInvariantGroup::LoopEnsures));
        if !entry.is_empty() {
            for h in &header {
                arcs.push(certified(
                    entry.iter().cloned(),
                    h.clone(),
                    format!("loop protocol: entry check licenses hypothesis of {}", a),
                ));
            }
        }
        if exports_at_exit && (!entry.is_empty() || !requires_entry) && !step.is_empty() {
            for x in &exit {
                arcs.push(certified(
                    entry.iter().chain(step.iter()).cloned(),
                    x.clone(),
                    format!(
                        "loop protocol ({}): {}latch/transfer checks license exit export of {}",
                        group.unwrap_or(LoopInvariantGroup::Invariant),
                        if requires_entry { "entry + " } else { "" },
                        a
                    ),
                ));
            }
        }
    }
    arcs
}

fn assert_query_protocol(rf: &RecordFacts<'_>) -> Vec<Arc> {
    let lemma = |section: ContractSection, point: AssertQueryPoint| EmissionRole::AssertQuery {
        section,
        point,
    };
    let mut arcs = Vec::new();
    for a in rf.by_artifact.keys() {
        let req_check = rf.at(a, &lemma(ContractSection::Requires, AssertQueryPoint::Check));
        for h in rf.at(a, &lemma(ContractSection::Requires, AssertQueryPoint::Assume)) {
            if !req_check.is_empty() {
                arcs.push(certified(
                    req_check.iter().cloned(),
                    h,
                    format!("lemma protocol: requires check licenses hypothesis of {}", a),
                ));
            }
        }
        let goal = rf.at(a, &lemma(ContractSection::Ensures, AssertQueryPoint::Check));
        for h in rf.at(a, &lemma(ContractSection::Ensures, AssertQueryPoint::Assume)) {
            if !goal.is_empty() {
                arcs.push(certified(
                    goal.iter().cloned(),
                    h,
                    format!("lemma protocol: proved goal licenses exported conclusion {}", a),
                ));
            }
        }
    }
    arcs
}

fn assert_protocol(rf: &RecordFacts<'_>) -> Vec<Arc> {
    // The pairing is construction-exact (producer walk), carried by the
    // shared `assertion` artifact.
    let mut arcs = Vec::new();
    for a in rf.by_artifact.keys() {
        let check = rf.at(a, &EmissionRole::Assertion { point: AssertionPoint::Check });
        for h in rf.at(a, &EmissionRole::Assertion { point: AssertionPoint::Establish }) {
            if !check.is_empty() {
                arcs.push(certified(
                    check.iter().cloned(),
                    h,
                    format!("assert protocol: discharged check licenses established fact {}", a),
                ));
            }
        }
    }
    arcs
}

fn assert_forall_protocol(rf: &RecordFacts<'_>) -> Vec<Arc> {
    let mut arcs = Vec::new();
    for a in rf.by_artifact.keys() {
        let goal = rf.at(a, &EmissionRole::AssertForall { point: ForallPoint::Goal });
        for h in rf.at(a, &EmissionRole::AssertForall { point: ForallPoint::Establish }) {
            if !goal.is_empty() {
                arcs.push(certified(
                    goal.iter().cloned(),
                    h,
                    format!("forall protocol: proved body licenses exported conclusion {}", a),
                ));
            }
        }
    }
    arcs
}

fn contract_callee(rf: &RecordFacts<'_>) -> Vec<Arc> {
    let mut arcs = Vec::new();
    for a in rf.by_artifact.keys() {
        let ens_checks = rf.at(a, &EmissionRole::FunctionEnsures);
        if !ens_checks.is_empty() {
            arcs.push(certified(
                ens_checks.iter().cloned(),
                a.clone(),
                format!("contract: callee's ensures checks license {}", a),
            ));
        }
    }
    arcs
}

/// Rule 6. One `CertifiedBy` arc per recorded checked export.
///
/// The record supplies the pairing; this function supplies only the claim that
/// the pairing licenses the export. Labels are namespaced for the combined
/// graph, and a row naming a label this record does not carry is skipped
/// rather than inventing a vertex.
fn checked_exports(rf: &RecordFacts<'_>) -> Vec<Arc> {
    let known: BTreeSet<&str> =
        rf.rows.iter().filter_map(|row| row.occurrence.label.as_deref()).collect();
    rf.record
        .checked_exports
        .iter()
        .filter(|export| {
            known.contains(export.check.as_str()) && known.contains(export.export.as_str())
        })
        .map(|export| {
            certified(
                [rf.ns(&export.check)],
                rf.ns(&export.export),
                format!(
                    "{}: discharged check licenses the assumption it admits",
                    match export.kind {
                        crate::record::CheckedExportKind::Assertion => "assert protocol",
                        crate::record::CheckedExportKind::GeneratedCheck =>
                            "generated check protocol",
                        crate::record::CheckedExportKind::InvariantBlock =>
                            "invariant block protocol",
                    }
                ),
            )
        })
        .collect()
}

fn is_call_post(o: &crate::record::Occurrence) -> bool {
    matches!(o.emission, Some(EmissionRole::CallPostcondition { .. }))
}

/// A callee precondition checked at a call, with the callee named. Rows whose
/// encoding did not name the callee cannot be paired with a call site.
fn is_call_pre(o: &crate::record::Occurrence) -> bool {
    matches!(o.emission, Some(EmissionRole::CallPrecondition { callee: Some(_), .. }))
}

/// One call-local licensing relation.
///
/// The relation is call-local — the head is *this* call's assumed
/// postcondition and the base is *this* call's licensor — but its precondition
/// tail is not refined per clause. Verus checks one aggregate `req%g(args)`
/// predicate per call, so the tail carries every precondition check the caller
/// discharged, not only the clauses the callee's own proof used.
///
/// Refining it needs a per-clause measurement that v0.1 does not take, and the
/// reason is symmetry (`PROOF_COVERAGE_GAPS.md` §4.1a). An
/// obligation terminal is obtained by *decomposing the formula the query
/// carries*; `req%g(args)` is an opaque predicate application whose body is not
/// in the query, so splitting it means unfolding a definition and re-lowering
/// the callee's clauses. The assumed `ens%g(args)` on the premise side is
/// opaque in exactly the same way. Unfolding one side and not the other buys
/// precision on the requires side while leaving the ensures side aggregated, so
/// the two are one change or neither.
#[derive(Clone, Debug)]
pub struct DemandCall {
    pub head: String,
    /// Ordinary call: callee ensures aggregate. Recursive call: decrease
    /// obligation. Missing for an unguarded/ambiguous recursive call.
    pub base: Option<String>,
    /// Every precondition check discharged at this call.
    pub checks: BTreeSet<String>,
    pub query: Option<u64>,
    pub caller: String,
    pub callee: Option<String>,
    pub node: Option<String>,
    pub recursive: bool,
}

/// Build the call-local relations consumed by the slicing fixed point.
pub fn demand_calls(rf: &RecordFacts<'_>) -> Vec<DemandCall> {
    let mut aggregate_checks: BTreeMap<(u64, String), BTreeSet<String>> = BTreeMap::new();
    for row in &rf.rows {
        let o = row.occurrence;
        if o.role == Role::Obligation && is_call_pre(o) {
            if let Some(node) = &o.node {
                aggregate_checks
                    .entry((row.query.id, node.clone()))
                    .or_default()
                    .insert(row.label.clone());
            }
        }
    }

    let mut out = Vec::new();
    for row in &rf.rows {
        let o = row.occurrence;
        if o.role != Role::Premise || !is_call_post(o) {
            continue;
        }
        let Some(node) = &o.node else { continue };
        let boundary = rf.call_sites.get(&(row.query.fun.clone(), node.clone()));
        let recursive = boundary.is_some_and(|call| call.recursive);
        let callee = boundary.and_then(|call| call.callee.clone()).or_else(|| match &o.emission {
            Some(EmissionRole::CallPostcondition { callee }) => Some(callee.clone()),
            _ => None,
        });

        let base = if recursive {
            let guard_node =
                rf.record.functions.iter().find(|function| function.fun == row.query.fun).and_then(
                    |function| {
                        function
                            .recursive_calls
                            .iter()
                            .find(|call| call.call_node == *node)
                            .map(|call| call.guard_node.as_str())
                    },
                );
            guard_node.and_then(|guard_node| {
                let guards: Vec<String> = rf
                    .rows
                    .iter()
                    .filter(|candidate| candidate.query.id == row.query.id)
                    .filter(|candidate| {
                        candidate.occurrence.role == Role::Obligation
                            && candidate.occurrence.node.as_deref() == Some(guard_node)
                            && matches!(
                                candidate.occurrence.emission,
                                Some(EmissionRole::TerminationCheck {
                                    at: TerminationPoint::Function
                                })
                            )
                            && candidate.occurrence.origin.kind != OriginKind::Unresolved
                    })
                    .map(|candidate| candidate.label.clone())
                    .collect();
                match guards.as_slice() {
                    [guard] => Some(guard.clone()),
                    _ => None,
                }
            })
        } else {
            row.artifact.clone()
        };

        let key = (row.query.id, node.clone());
        let checks = aggregate_checks.get(&key).cloned().unwrap_or_default();
        out.push(DemandCall {
            head: row.label.clone(),
            base,
            checks,
            query: Some(row.query.id),
            caller: row.query.fun.clone(),
            callee,
            node: Some(node.clone()),
            recursive,
        });
    }
    out
}
