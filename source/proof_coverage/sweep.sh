#!/usr/bin/env bash
# Construct-provenance sweep: run every probe through the instrumented
# verifier and print the per-family provenance-quality table for each.
#
# This is the "stare between two stages" instrument: it measures whether
# occurrence provenance is established (family, span, CFG node, artifact
# join) for each language construct, without needing any solver evidence.
# Unresolved rows print their shapes — that list is the gap worklist.
#
# Usage: ./sweep.sh [probe.rs ...]        (default: probes/*.rs + ../../examples)
set -u
ARGS=()
for a in "$@"; do
    ARGS+=("$(realpath "$a")")
done
cd "$(dirname "$0")/.."   # source/
VERUS=./target-verus/release/verus
AUDIT=./target-verus/release/pc_audit
ANALYZE=./target-verus/release/pc_analyze
FAILED=0

probes=("${ARGS[@]:-}")
if [ -z "${probes[0]:-}" ]; then
    probes=(proof_coverage/probes/*.rs)
fi

for probe in "${probes[@]}"; do
    name=$(basename "$probe" .rs)
    out="/tmp/pc_sweep_${name}.json"
    rm -f "$out"
    if ! timeout 120 env VERUS_PROOF_COVERAGE_OUT="$out" \
        "$VERUS" "$probe" -V proof-coverage > "/tmp/pc_sweep_${name}.log" 2>&1; then
        echo "== $name: VERIFICATION FAILED (probe must verify; see /tmp/pc_sweep_${name}.log) =="
        FAILED=1
        continue
    fi
    echo "== $name =="
    "$AUDIT" --families "$out" | tail -n +2
    if ! "$AUDIT" "$out" > "/tmp/pc_sweep_${name}.audit" 2>&1; then
        echo "  AUDIT VIOLATIONS:"
        grep -A 100 "VIOLATIONS" "/tmp/pc_sweep_${name}.audit" | head -20
        FAILED=1
    fi
    if [ "$name" = source_projection_constructs ]; then
        local_gaps=$(
            "$ANALYZE" "$out" report |
                jq '[.analysis_coverage.instrumentation_gaps[] | select(.locality == "local")] | length'
        )
        if [ "$local_gaps" -ne 0 ]; then
            echo "  SOURCE PROJECTION VIOLATION: $local_gaps local artifacts are unmeasured"
            FAILED=1
        fi
        tail_return_spans=$(
            jq '[
                .artifacts[]
                | select(
                    .kind == "return_binding"
                    and (.id | endswith("::tail_bool#return.src0"))
                    and .cfg_node != null
                )
                | (
                    .span
                    | capture(":(?<start>[0-9]+):[0-9]+: (?<end>[0-9]+):[0-9]+")
                )
                | select(.start == .end)
            ] | length' "$out"
        )
        if [ "$tail_return_spans" -ne 1 ]; then
            echo "  SOURCE PROJECTION VIOLATION: tail return does not retain its expression span"
            FAILED=1
        fi
        tuple_return_spans=$(
            jq '[
                .artifacts[]
                | select(
                    .kind == "return_binding"
                    and (.id | endswith("::tail_tuple_after_mut#return.src0"))
                    and .cfg_node != null
                )
                | (
                    .span
                    | capture(":(?<start>[0-9]+):[0-9]+: (?<end>[0-9]+):[0-9]+")
                )
                | select(.start == .end)
            ] | length' "$out"
        )
        if [ "$tuple_return_spans" -ne 1 ]; then
            echo "  SOURCE PROJECTION VIOLATION: tuple tail after mutable parameter does not retain its expression span"
            FAILED=1
        fi
        unit_return_bindings=$(
            jq '[
                .artifacts[]
                | select(
                    .kind == "return_binding"
                    and (
                        (.id | contains("::pattern_and_control_probe#return."))
                        or (.id | contains("::unit_tail_branch#return."))
                    )
                )
            ] | length' "$out"
        )
        if [ "$unit_return_bindings" -ne 0 ]; then
            echo "  SOURCE PROJECTION VIOLATION: unit-valued returns were inventoried as return bindings"
            FAILED=1
        fi
    fi
done
exit $FAILED
