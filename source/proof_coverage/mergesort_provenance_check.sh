#!/usr/bin/env bash
# End-to-end regression for exact SST -> AIR lineage and typed identity joins.
set -euo pipefail
cd "$(dirname "$0")/.." # source/

V=${PC_VERUS:-./target-verus/release/verus}
U=${PC_AUDIT:-./target-verus/release/pc_audit}
if [ -n "${PC_MERGESORT_OUT:-}" ]; then
  OUT=$PC_MERGESORT_OUT
  cleanup=false
else
  OUT=$(mktemp "${TMPDIR:-/tmp}/proof-coverage-mergesort.XXXXXX.json")
  cleanup=true
fi
if $cleanup; then
  trap 'rm -f "$OUT"' EXIT
fi

timeout 180 env VERUS_PROOF_COVERAGE_OUT="$OUT" \
  "$V" ../examples/mergesort.rs -V proof-coverage >/dev/null
"$U" "$OUT" >/dev/null

jq -e '
  def merge_batch:
    .queries[]
    | select(
        .family == "batch"
        and .fun == "mergesort::merge"
        and .desc == "function body check"
      );

  (merge_batch) as $batch
  | (
      $batch.occurrences[]
      | select(
          .role == "obligation"
          and .origin.detail == "assertion"
          and ((.span // "") | contains(":135:"))
        )
    ) as $goal
  | (
      .queries[]
      | select(
          .family == "focused"
          and .parent_obligation_label == $goal.label
        )
    ) as $focused
  | ($focused.core // []) as $core
  | [
      $batch.occurrences[]
      | select(.label as $label | $core | index($label))
    ] as $selected
  | [
      .derivations[]
      | select(.transform == "lower_statement")
      | .outputs[]
    ] as $lowered
  | .schema == "verus-proof-coverage/1"
    and .artifact_version == "0.1"
    and .summary.unresolved_premises == 0
    and .summary.unresolved_obligations == 0
    and all(.queries[]; .shadow_result == "valid")
    and $focused.shadow_result == "valid"
    and all($selected[]; .origin.kind != "unresolved")
    and any(
      $selected[];
      .emission == {"kind": "branch_condition", "arm": 1}
      and .node == "r.b0.b6.c.b2"
    )
    and any(
      $selected[];
      .emission == {"kind": "loop_exit_condition"}
      and .node == "r.b0.b6.x"
    )
    and any(
      $selected[];
      .origin.detail == "sst:VarEquality"
      and .rule == "sst.exact_lowering"
    )
    and any(
      $selected[];
      .origin.detail == "sst:MutRefCurrent"
      and .rule == "sst.exact_lowering"
    )
    and all(
      $selected[]
      | select(
          .rule == "sst.exact_lowering"
        );
      .label as $label | $lowered | index($label)
    )
' "$OUT" >/dev/null

echo "mergesort provenance clean"
