#!/usr/bin/env bash
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
OUT=$(mktemp -d "${TMPDIR:-/tmp}/proof-coverage-analysis-v01.XXXXXX")
trap 'rm -rf "$OUT"' EXIT

"$HERE/run.sh" "$OUT" >/dev/null

while IFS=$'\t' read -r file expected; do
    [[ -z "$file" || "$file" == \#* ]] && continue
    if ! grep -F -- "$expected" "$OUT/$file/findings.txt" >/dev/null; then
        echo "missing expected signal in $file: $expected" >&2
        exit 1
    fi
done <"$HERE/expected-signals.txt"

while IFS=$'\t' read -r file forbidden; do
    [[ -z "$file" || "$file" == \#* ]] && continue
    if grep -F -- "$forbidden" "$OUT/$file/findings.txt" >/dev/null; then
        echo "unexpected signal in $file: $forbidden" >&2
        exit 1
    fi
done <"$HERE/forbidden-signals.txt"

joint_function=$(awk \
    '/^function joint::joint_chain$/{seen++; next} seen >= 2 {print}' \
    "$OUT/joint/findings.txt")
if ! grep -F -- \
    "finding goal-unused-precondition artifact=joint::joint_chain#req[2]" \
    <<<"$joint_function" >/dev/null; then
    echo "joint function finding is not scoped to its selected root" >&2
    exit 1
fi

trait_function=$(awk \
    '/^function trait_boundary::use_increment$/{seen++; next} seen >= 2 {print}' \
    "$OUT/trait_boundary/findings.txt")
if grep -F -- \
    "finding available-not-observed artifact=trait_boundary::use_increment#req[0]" \
    <<<"$trait_function" >/dev/null; then
    echo "trait caller requirement was incorrectly uncovered at function scope" >&2
    exit 1
fi

# The assert certificate must carry the requirements into the root slice:
# they are transitive at function scope, not available-not-observed.
established_function=$(awk \
    '/^function established::established$/{seen++; next} seen >= 2 {print}' \
    "$OUT/established/findings.txt")
if grep -F -- \
    "finding available-not-observed artifact=established::established#req" \
    <<<"$established_function" >/dev/null; then
    echo "established-assert requirement was incorrectly uncovered at function scope" >&2
    exit 1
fi
if ! grep -F -- \
    "established::established#req[0] @ function.requires" \
    <<<"$established_function" >/dev/null; then
    echo "established-assert requirement missing from the function transitive slice" >&2
    exit 1
fi

SOURCE=$(cd "$HERE/../../.." && pwd)
ANALYZE=${PC_ANALYZE:-"$SOURCE/target-verus/release/pc_analyze"}
"$ANALYZE" \
    "$OUT/trait_boundary/record.json" \
    "$OUT/trait_boundary/record.json" \
    study use_increment opaque >"$OUT/trait_boundary/multi-findings.txt"
if [[ $(grep -c '^function trait_boundary::use_increment$' \
    "$OUT/trait_boundary/multi-findings.txt") -ne 4 ]]; then
    echo "multi-record study merged or dropped same-named function scopes" >&2
    exit 1
fi
if [[ $(grep -Fxc \
    'observation available-not-observed artifact=trait_boundary::use_increment#req[0]' \
    "$OUT/trait_boundary/multi-findings.txt") -ne 2 ]]; then
    echo "multi-record function finding comparison ignored record identity" >&2
    exit 1
fi

echo "analysis v0.1 study matches"
