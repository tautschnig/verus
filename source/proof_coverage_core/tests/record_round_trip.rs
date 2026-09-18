//! The record is a round-trippable observation.
//!
//! Before the schema was `Serialize + Deserialize`, no consumer could share
//! the producer's types, so each one re-declared a "tolerant subset" and
//! recovered semantics by parsing strings. This test states the invariant
//! that makes those private schemas unnecessary: a real record deserializes
//! into `record::CoverageRecord` and serializes back to the same bytes,
//! `record_id` included.

use proof_coverage_core::record::CoverageRecord;
use std::path::{Path, PathBuf};

fn fixture_dir() -> PathBuf {
    match std::env::var_os("PC_RECORD_FIXTURES") {
        Some(dir) => PathBuf::from(dir),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures"),
    }
}

fn records() -> Vec<(String, String)> {
    let dir = fixture_dir();
    let mut found = Vec::new();
    let entries = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read record fixtures at {}: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("readable dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        found.push((name, std::fs::read_to_string(&path).expect("readable fixture")));
    }
    found.sort();
    assert!(!found.is_empty(), "no record fixtures in {}", dir.display());
    found
}

#[test]
fn records_round_trip_byte_identically() {
    for (name, text) in records() {
        let parsed: CoverageRecord = serde_json::from_str(&text)
            .unwrap_or_else(|e| panic!("{name} does not deserialize into the schema: {e}"));

        let reserialized = serde_json::to_string_pretty(&parsed)
            .unwrap_or_else(|e| panic!("{name} reserializes: {e}"));

        assert_eq!(
            reserialized.trim_end(),
            text.trim_end(),
            "{name} did not survive a schema round trip"
        );
    }
}

/// The identity field must be carried by the schema, not reconstructed. If
/// `record_id` were dropped on deserialization, every consumer would have to
/// reach around the schema into raw JSON to recover it.
#[test]
fn record_identity_survives_the_schema() {
    for (name, text) in records() {
        let raw: serde_json::Value = serde_json::from_str(&text).expect("valid JSON");
        let expected = raw.get("record_id").and_then(serde_json::Value::as_str);
        let expected = expected.unwrap_or_else(|| panic!("{name} has no record_id"));

        let parsed: CoverageRecord = serde_json::from_str(&text).expect("parses");
        assert_eq!(parsed.record_id, expected, "{name} lost its identity");

        proof_coverage_core::audit::verify_record_id(&raw)
            .unwrap_or_else(|e| panic!("{name}: recorded identity does not verify: {e}"));
    }
}

/// A second pass must be a fixed point: parsing what we produced yields an
/// equal value. This catches a field that serializes but silently normalizes.
#[test]
fn round_trip_is_idempotent() {
    for (name, text) in records() {
        let first: CoverageRecord = serde_json::from_str(&text).expect("first parse");
        let once = serde_json::to_string(&first).expect("first serialize");
        let second: CoverageRecord = serde_json::from_str(&once).expect("second parse");
        assert_eq!(first, second, "{name} is not a round-trip fixed point");
    }
}

/// The typed schema must reject a value outside a closed set rather than
/// silently accepting it as a string. This is the property that lets the
/// analyzer stop defending against unknown spellings.
#[test]
fn unknown_enum_spellings_are_rejected() {
    let (name, text) = records().into_iter().next().expect("at least one fixture");
    let mut value: serde_json::Value = serde_json::from_str(&text).unwrap();

    let queries = value["queries"].as_array_mut().expect("queries array");
    let query = queries.first_mut().expect("at least one query");
    query["family"] = serde_json::Value::String("not_a_family".to_string());

    let parsed: Result<CoverageRecord, _> = serde_json::from_value(value);
    assert!(parsed.is_err(), "{name}: an invalid query family was accepted");
}

/// Every value the schema can express is either observed in the fixture
/// corpus or explicitly declared unobserved.
///
/// This makes the fallback inventory executable. A variant listed here as
/// unobserved is a fallback no measured Verus run produced; if one starts
/// appearing, this test fails and the inventory must be updated rather than
/// quietly drifting. Conversely, adding a variant without a fixture that
/// exercises it fails immediately.
#[test]
fn fixture_corpus_covers_every_schema_variant() {
    use proof_coverage_core::record::{
        ArtifactKind, Carrier, CfgEdgeKind, CfgNodeKind, LoopInvariantGroup, OriginKind,
        QueryFamily, Role, Transform,
    };

    let parsed: Vec<CoverageRecord> =
        records().iter().map(|(_, text)| serde_json::from_str(text).expect("parses")).collect();

    let mut artifact_kinds = Vec::new();
    let mut groups = Vec::new();
    let mut carriers = Vec::new();
    let mut origins = Vec::new();
    let mut roles = Vec::new();
    let mut families = Vec::new();
    let mut transforms = Vec::new();
    let mut node_kinds = Vec::new();
    let mut edge_kinds = Vec::new();

    for record in &parsed {
        for artifact in &record.artifacts {
            artifact_kinds.push(artifact.kind);
            groups.extend(artifact.group);
        }
        for query in &record.queries {
            families.push(query.family);
            for occurrence in &query.occurrences {
                carriers.push(occurrence.carrier);
                origins.push(occurrence.origin.kind);
                roles.push(occurrence.role);
            }
        }
        for derivation in &record.derivations {
            transforms.push(derivation.transform);
        }
        for function in &record.functions {
            for node in &function.cfg.nodes {
                node_kinds.push(node.kind);
            }
            for edge in &function.cfg.edges {
                edge_kinds.push(edge.kind);
            }
        }
    }

    fn assert_coverage<T>(all: &'static [T], observed: &[T], unobserved: &[T], label: &str)
    where
        T: PartialEq + std::fmt::Debug,
    {
        for variant in all {
            let seen = observed.contains(variant);
            let declared_absent = unobserved.contains(variant);
            assert!(
                seen != declared_absent,
                "{label}: {variant:?} is {} but declared {}",
                if seen { "observed" } else { "unobserved" },
                if declared_absent { "unobserved" } else { "observed" }
            );
        }
    }

    assert_coverage(ArtifactKind::ALL, &artifact_kinds, &[], "ArtifactKind");
    assert_coverage(Carrier::ALL, &carriers, &[], "Carrier");
    // `Unresolved` is the typed gap for a row no exact rule attributes. With
    // the declaration-level sidecar covering query-local axioms, the 33-record
    // corpus has zero such rows, so this fixture set does not exercise it. It
    // is not a fallback: a construct the sidecars do not yet cover would
    // produce it again, and this test would then require the corpus to say so.
    assert_coverage(OriginKind::ALL, &origins, &[OriginKind::Unresolved], "OriginKind");
    assert_coverage(Role::ALL, &roles, &[], "Role");
    assert_coverage(QueryFamily::ALL, &families, &[], "QueryFamily");
    assert_coverage(CfgNodeKind::ALL, &node_kinds, &[], "CfgNodeKind");
    assert_coverage(CfgEdgeKind::ALL, &edge_kinds, &[], "CfgEdgeKind");

    // `(false, false)` — a loop invariant clause declared neither at entry
    // nor at exit. No measured run has produced one.
    assert_coverage(
        LoopInvariantGroup::ALL,
        &groups,
        &[LoopInvariantGroup::Unclassified],
        "LoopInvariantGroup",
    );

    // The conservative order-alignment fallback. Exact lowering provenance
    // supersedes it, so no measured run emits it.
    assert_coverage(Transform::ALL, &transforms, &[Transform::LowerAssume], "Transform");
}
