#!/usr/bin/env bash
# One-command v0.1 artifact check: frozen explanations/findings/reports,
# audits, construct sweep, controlled sensitivity, byte-determinism, and
# the sibling visualizer contract when it is available.
# Exit 0 = everything the artifact claims is reproduced.
set -uo pipefail
cd "$(dirname "$0")/.."   # source/
V=./target-verus/release/verus
R=./target-verus/release/rust_verify
A=./target-verus/release/pc_analyze
U=./target-verus/release/pc_audit
REPO=$(cd .. && pwd)
VISUALIZER=${PC_VISUALIZER_DIR:-"$(cd ../.. && pwd)/visualizer"}
OUT=$(mktemp -d "${TMPDIR:-/tmp}/proof-coverage-v01.XXXXXX")
trap 'rm -rf "$OUT"' EXIT
fail=0
step() { echo "== $1"; }
source_fingerprint() {
  find . -path ./target-verus -prune -o \
    -type f \( -name '*.rs' -o -name Cargo.toml -o -name Cargo.lock \) -print0 \
    | LC_ALL=C sort -z \
    | xargs -0 sha256sum \
    | sha256sum
}
write_build_manifest() {
  destination=$1
  jq -n \
    --arg source_fingerprint "${source_built%% *}" \
    --arg verus_sha256 "$(sha256sum "$V" | cut -d' ' -f1)" \
    --arg rust_verify_sha256 "$(sha256sum "$R" | cut -d' ' -f1)" \
    --arg pc_analyze_sha256 "$(sha256sum "$A" | cut -d' ' -f1)" \
    --arg pc_audit_sha256 "$(sha256sum "$U" | cut -d' ' -f1)" \
    '{
      schema: "verus-proof-coverage-build/0.1",
      artifact_version: "0.1",
      source_fingerprint: $source_fingerprint,
      binaries: {
        verus: $verus_sha256,
        rust_verify: $rust_verify_sha256,
        pc_analyze: $pc_analyze_sha256,
        pc_audit: $pc_audit_sha256
      }
    }' > "$destination"
}

step "1/12 build release binaries used by this gate"
source_before=$(source_fingerprint)
if ! cargo build --release -p verus -p rust_verify -p proof_coverage --bins; then
  echo "RELEASE BUILD FAILED; refusing to run existing binaries"
  exit 1
fi
source_built=$(source_fingerprint)
if [ "$source_before" != "$source_built" ]; then
  echo "SOURCE CHANGED DURING RELEASE BUILD; refusing to run mismatched binaries"
  exit 1
fi
if [ ! -x "$V" ] || [ ! -x "$R" ] || [ ! -x "$A" ] || [ ! -x "$U" ]; then
  echo "RELEASE BUILD DID NOT PRODUCE verus, rust_verify, pc_analyze, and pc_audit"
  exit 1
fi
candidate_manifest="$OUT/proof-coverage-v01-build.json"
write_build_manifest "$candidate_manifest"

step "2/12 proof-coverage Cargo tests"
# Not `--lib`: the record round-trip and L2/L3 layering suites are integration
# tests over the checked-in record corpus, and `--lib` silently skipped them.
# A wire-format change that stales those fixtures must fail this gate.
cargo test -p proof_coverage_core -p proof_coverage \
  && cargo test -p vir --lib \
  && cargo check -p rust_verify --no-default-features --tests \
  || { echo "CARGO TESTS FAILED"; fail=1; }

step "3/12 frozen explanation traces and induction notes"
./proof_coverage/fixtures/check.sh || fail=1

step "4/12 construct sweep (all probes verify; per-family provenance; audits)"
if ./proof_coverage/sweep.sh > "$OUT/sweep.log" 2>&1; then
  echo "sweep clean"
else
  echo "SWEEP FAILED"
  tail -n 40 "$OUT/sweep.log"
  fail=1
fi

step "5/12 record audits over the example corpus"
ok=1
audit_records=()
for ex in recursion invariants datatypes calc quantifiers assorted_demo; do
  record="$OUT/audit_$ex.json"
  audit_records+=("$record")
  if ! timeout 120 env VERUS_PROOF_COVERAGE_OUT="$record" \
      $V ../examples/$ex.rs -V proof-coverage >"$OUT/audit_$ex.log" 2>&1; then
    echo "verification failed for examples/$ex.rs"
    tail -n 20 "$OUT/audit_$ex.log"
    ok=0
  fi
done
if [ $ok -eq 1 ] && $U "${audit_records[@]}" >"$OUT/audit.log" 2>&1; then
  echo "audits clean"
else
  echo "AUDIT FAILED"
  [ -f "$OUT/audit.log" ] && cat "$OUT/audit.log"
  fail=1
fi

step "6/12 exact lowering provenance on mergesort"
./proof_coverage/emission_slot_check.sh \
  || { echo "EMISSION SLOT CHECK FAILED"; fail=1; }
./proof_coverage/mergesort_provenance_check.sh \
  || { echo "MERGESORT PROVENANCE FAILED"; fail=1; }

step "7/12 byte-determinism under parallel verification"
if timeout 120 env VERUS_PROOF_COVERAGE_OUT="$OUT/parallel.json" \
    $V proof_coverage/probes/parallel_buckets.rs -V proof-coverage >/dev/null 2>&1 \
  && timeout 120 env VERUS_PROOF_COVERAGE_OUT="$OUT/serial.json" \
    $V proof_coverage/probes/parallel_buckets.rs -V proof-coverage \
      --num-threads 1 >/dev/null 2>&1 \
  && diff -q "$OUT/parallel.json" "$OUT/serial.json" >/dev/null; then
  echo "parallel == serial (byte-identical)"
else
  echo "DETERMINISM FAILED"
  fail=1
fi

step "8/12 controlled postcondition sensitivity"
PC_POSTCONDITION_SLICE_OUT="$OUT/postcondition" \
  ./proof_coverage/postcondition_slice_check.sh \
  && echo "postcondition sensitivity clean" || { echo "POSTCONDITION CHECK FAILED"; fail=1; }

step "9/12 frozen query/function/project report contract"
if timeout 120 env VERUS_PROOF_COVERAGE_OUT="$OUT/call.json" \
    $V proof_coverage/probes/call_residue.rs -V proof-coverage >/dev/null 2>&1 \
  && $A "$OUT/postcondition/strong.json" "$OUT/postcondition/weak.json" \
    "$OUT/call.json" project > "$OUT/project.json" \
  && jq -S '{
  schema, level, record_count, record_versions, call_policy, project,
  query_statuses: (
    .queries | group_by(.status)
    | map({key: .[0].status, value: length}) | from_entries
  ),
  function_statuses: (
    .functions | group_by(.status)
    | map({key: .[0].status, value: length}) | from_entries
  ),
  completeness: {
    queries: {
      attribution_partial: ([.queries[] | select(.completeness.attribution.status == "Partial")] | length),
      placement_partial: ([.queries[] | select(.completeness.placement.status == "Partial")] | length),
      artifact_partial: ([.queries[] | select(.completeness.artifact_projection.status == "Partial")] | length),
      licensing_partial: ([.queries[] | select(.completeness.licensing.status == "Partial")] | length)
    },
    functions: {
      attribution_partial: ([.functions[] | select(.completeness.attribution.status == "Partial")] | length),
      placement_partial: ([.functions[] | select(.completeness.placement.status == "Partial")] | length),
      artifact_partial: ([.functions[] | select(.completeness.artifact_projection.status == "Partial")] | length),
      licensing_partial: ([.functions[] | select(.completeness.licensing.status == "Partial")] | length)
    }
  },
  finding_kinds: (
    [.functions[].findings[]? | .kind] | group_by(.)
    | map({key: .[0], value: length}) | from_entries
  ),
  findings_withheld: ([.functions[].findings[]? | select(.defensible == false)] | length)
}' "$OUT/project.json" > "$OUT/project.summary.json" \
  && diff -q proof_coverage/fixtures/v01_project_report.json \
    "$OUT/project.summary.json" >/dev/null; then
  echo "v0.1 report contract matches"
else
  echo "V0.1 REPORT DRIFT"
  if [ -f "$OUT/project.summary.json" ]; then
    diff -u proof_coverage/fixtures/v01_project_report.json \
      "$OUT/project.summary.json" > "$OUT/project.diff" || true
    head -n 80 "$OUT/project.diff"
  fi
  fail=1
fi

step "10/12 minimal findings and intraprocedural analysis studies"
./proof_coverage/demo/check.sh \
  || { echo "QUERY FINDINGS DEMO DRIFT"; fail=1; }
./proof_coverage/studies/analysis_v01/check.sh \
  || { echo "ANALYSIS V0.1 STUDY DRIFT"; fail=1; }

if [ -f "$VISUALIZER/package.json" ]; then
  step "11/12 visualizer unit and fixture checks"
  (cd "$VISUALIZER" && npm test && npm run check) \
    || { echo "VISUALIZER UNIT/CHECK FAILED"; fail=1; }

  step "12/12 visualizer live end-to-end check"
  (cd "$VISUALIZER" \
    && PC_VERUS_DIR="$REPO" PC_BUILD_MANIFEST="$candidate_manifest" npm run test:e2e) \
    || { echo "VISUALIZER E2E FAILED"; fail=1; }
else
  step "11/12 visualizer unit and fixture checks (skipped: sibling absent)"
  step "12/12 visualizer live end-to-end check (skipped: sibling absent)"
fi

source_final=$(source_fingerprint)
if [ "$source_final" != "$source_built" ]; then
  echo "SOURCE CHANGED AFTER RELEASE BUILD; gate results do not describe the current tree"
  fail=1
fi

if [ $fail -eq 0 ]; then
  manifest=target-verus/release/proof-coverage-v01-build.json
  cp "$candidate_manifest" "$manifest"
  echo "accepted build manifest: $manifest"
  echo "ARTIFACT OK"
else
  echo "ARTIFACT FAILED"
fi
exit $fail
