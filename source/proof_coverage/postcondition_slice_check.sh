#!/usr/bin/env bash
# Controlled witness-relative check: weakening an independent postcondition
# removes its uniquely needed source requirement from the function slice.
set -euo pipefail

cd "$(dirname "$0")/.."
VERUS=./target-verus/release/verus
ANALYZE=./target-verus/release/pc_analyze
OUT="${PC_POSTCONDITION_SLICE_OUT:-/tmp/proof-coverage-postcondition-slice}"
mkdir -p "$OUT"

for strength in strong weak; do
    record="$OUT/$strength.json"
    env VERUS_PROOF_COVERAGE_OUT="$record" \
        "$VERUS" "proof_coverage/probes/postcondition_slice_${strength}.rs" \
        -V proof-coverage >/dev/null
    "$ANALYZE" "$record" report opaque >"$OUT/$strength.report.json"
    jq -r '
        .functions[]
        | select(.function | endswith("::compare"))
        | .definite_artifacts[]
        | sub("^.*::compare"; "compare")
    ' "$OUT/$strength.report.json" | sort -u >"$OUT/$strength.artifacts"
done

# The return-value binding is in both slices: the postcondition speaks about
# the returned value in both versions. Only the requirement differs.
printf '%s\n' 'compare#req[0]' 'compare#req[1]' 'compare#return.src0' >"$OUT/strong.expected"
printf '%s\n' 'compare#req[1]' 'compare#return.src0' >"$OUT/weak.expected"
cmp "$OUT/strong.expected" "$OUT/strong.artifacts"
cmp "$OUT/weak.expected" "$OUT/weak.artifacts"

echo "postcondition slice check: strong uses req[0]+req[1]; weak uses req[1] only"
