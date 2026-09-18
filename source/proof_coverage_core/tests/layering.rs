//! The L2/L3 layering is a property of the code, stated over real records.
//!
//! `facts` must produce no licensing arc, `licensing` must produce only
//! licensing arcs whose heads are premises or artifacts, and the composed
//! graph must pass its own structural check. Runs over the same fixture
//! corpus as `record_round_trip`.

use proof_coverage_core::analysis::{self, ArcKind};
use proof_coverage_core::facts;
use proof_coverage_core::licensing::LicensingRule;
use proof_coverage_core::record::CoverageRecord;
use proof_coverage_core::record::{QueryFamily, Role};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

fn records() -> Vec<(String, CoverageRecord)> {
    let dir = match std::env::var_os("PC_RECORD_FIXTURES") {
        Some(dir) => PathBuf::from(dir),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures"),
    };
    let mut found = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("fixture dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let text = std::fs::read_to_string(&path).expect("readable");
        found.push((name, serde_json::from_str(&text).expect("parses")));
    }
    found.sort_by(|a, b| a.0.cmp(&b.0));
    assert!(!found.is_empty());
    found
}

/// L2 is policy-free: the fact graph contains evidence and structure only.
#[test]
fn facts_contain_no_licensing() {
    for (name, record) in records() {
        let f = facts::facts(std::slice::from_ref(&record));
        for arc in &f.arcs {
            assert!(
                matches!(
                    arc.kind,
                    ArcKind::SupportedBy
                        | ArcKind::ObservedInBatch
                        | ArcKind::TerminalOf
                        | ArcKind::Aggregates
                ),
                "{name}: fact graph carries a {} arc ({})",
                arc.kind,
                arc.why
            );
        }
        assert_eq!(f.records.len(), 1);
    }
}

/// L3 is licensing only: every rule produces `CertifiedBy` arcs whose heads
/// are premises or artifacts, never obligations; and every rule is one the
/// enumeration names.
#[test]
fn licensing_rules_certify_premises_and_artifacts_only() {
    for (name, record) in records() {
        let f = facts::facts(std::slice::from_ref(&record));
        let rf = &f.records[0];
        for rule in LicensingRule::ALL {
            for arc in rule.arcs(rf, &f) {
                assert_eq!(
                    arc.kind,
                    ArcKind::CertifiedBy,
                    "{name}: rule {} produced a {} arc",
                    rule.name(),
                    arc.kind
                );
                for head in &arc.head {
                    assert!(
                        !f.obligations.contains(head),
                        "{name}: rule {} licenses obligation {head}",
                        rule.name()
                    );
                    assert!(
                        f.premises.contains(head) || f.artifact_ids.contains(head),
                        "{name}: rule {} licenses {head}, which is neither a premise nor an artifact",
                        rule.name()
                    );
                }
            }
        }
    }
}

/// The composed graph satisfies its own structural invariants. Demand-refined
/// calls are not materialized as static fact/licensing arcs.
#[test]
fn composed_graph_checks_without_induction_certificates() {
    for (name, record) in records() {
        let g = analysis::build(std::slice::from_ref(&record));
        assert!(g.check().is_empty(), "{name}: {:?}", g.check());
        assert!(
            g.arcs.iter().all(|arc| arc.kind != ArcKind::Demand),
            "{name}: demand relation was incorrectly materialized as a static arc"
        );
    }
}

/// A batch core is one joint set-to-set observation. It must not be expanded
/// into one prefix-filtered edge per obligation.
#[test]
fn batch_evidence_is_one_joint_observation() {
    for (name, record) in records() {
        let f = facts::facts(std::slice::from_ref(&record));
        let roles: BTreeMap<&str, Role> = record
            .queries
            .iter()
            .flat_map(|query| &query.occurrences)
            .filter_map(|occurrence| {
                occurrence.label.as_deref().map(|label| (label, occurrence.role))
            })
            .collect();

        for query in record.queries.iter().filter(|query| query.family == QueryFamily::Batch) {
            let Some(core) = &query.core else { continue };
            let members: BTreeSet<&str> = core.iter().map(String::as_str).collect();
            let expected_head: BTreeSet<String> = members
                .iter()
                .filter(|label| roles.get(**label) == Some(&Role::Obligation))
                .map(|label| (*label).to_string())
                .collect();
            let mut expected_tail: BTreeSet<String> = BTreeSet::from([format!("β:{}", query.id)]);
            expected_tail.extend(
                members
                    .iter()
                    .filter(|label| roles.get(**label) != Some(&Role::Obligation))
                    .map(|label| (*label).to_string()),
            );

            let arcs: Vec<_> = f
                .arcs
                .iter()
                .filter(|arc| arc.kind == ArcKind::ObservedInBatch && arc.query == Some(query.id))
                .collect();
            if expected_head.is_empty() {
                assert!(arcs.is_empty(), "{name}: q{} has a headless batch arc", query.id);
            } else {
                assert_eq!(
                    arcs.len(),
                    1,
                    "{name}: q{} expanded one batch witness into {} arcs",
                    query.id,
                    arcs.len()
                );
                assert_eq!(arcs[0].head, expected_head, "{name}: q{} batch heads", query.id);
                assert_eq!(arcs[0].tail, expected_tail, "{name}: q{} batch tail", query.id);
            }
        }
    }
}

/// The focused query is the precise source of branch- and SSA-aware scope.
/// Its batch parent and every terminal child expose the same available facts.
#[test]
fn terminals_inherit_parent_obligation_scope() {
    for (name, record) in records() {
        let f = facts::facts(std::slice::from_ref(&record));
        for query in record.queries.iter().filter(|query| query.family == QueryFamily::Focused) {
            let parent = query.parent_obligation_label.as_ref().expect("audited parent label");
            let target = query.target_label.as_ref().expect("audited target label");
            let parent_scope = f
                .obligation_scopes
                .get(parent)
                .unwrap_or_else(|| panic!("{name}: q{} parent {parent} has no scope", query.id));
            let terminal_scope = f
                .obligation_scopes
                .get(target)
                .unwrap_or_else(|| panic!("{name}: q{} terminal {target} has no scope", query.id));
            let mut expected: BTreeSet<String> = query.available.iter().cloned().collect();
            expected.remove(target);

            assert_eq!(parent_scope.available, expected, "{name}: q{} parent scope", query.id);
            assert_eq!(
                terminal_scope.available, parent_scope.available,
                "{name}: q{} terminal did not inherit parent scope",
                query.id
            );
            assert_eq!(terminal_scope.ambients, parent_scope.ambients);
            assert_eq!(terminal_scope.solver_context, parent_scope.solver_context);
            assert_eq!(parent_scope.terminal_path, None);
            assert_eq!(terminal_scope.terminal_path, query.terminal_path);
        }
    }
}
