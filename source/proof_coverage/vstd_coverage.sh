#!/usr/bin/env bash
# Scale run: verify all of vstd with the proof-coverage observer, audit the
# record, and print the population summary. This is the same invocation
# vstd_build uses, with the observer on and outputs redirected so the built
# vstd is untouched.
#
# Usage: ./proof_coverage/vstd_coverage.sh [OUTDIR]     (default /tmp/vstd-pc)
set -euo pipefail
cd "$(dirname "$0")/.."   # source/
OUT=${1:-/tmp/vstd-pc}
mkdir -p "$OUT"
R=$(realpath target-verus/release)
V=./target-verus/release/verus
U=./target-verus/release/pc_audit

time env RUST_MIN_STACK=$((10 * 1024 * 1024)) VERUS_PROOF_COVERAGE_OUT="$OUT/vstd.json" \
  "$V" --internal-test-mode \
  --extern verus_builtin="$R/libverus_builtin.rlib" \
  --extern verus_builtin_macros="$R/libverus_builtin_macros.so" \
  --extern verus_state_machines_macros="$R/libverus_state_machines_macros.so" \
  --crate-type=lib --export "$OUT/vstd.vir" --out-dir "$OUT" \
  --multiple-errors 2 --is-vstd --compile -C opt-level=3 \
  --cfg 'feature="std"' --cfg 'feature="alloc"' --cfg 'feature="nonzero_internals"' \
  -V proof-coverage vstd/vstd.rs > "$OUT/verus.log" 2>&1
grep -E "^proof-coverage:|^verification results" "$OUT/verus.log"
"$U" "$OUT/vstd.json" | grep -E "queries|occurrences|placement|friendly|audit"

echo "--- shadow results ---"
jq -r '.queries[] | .shadow_result // "null"' "$OUT/vstd.json" | sort | uniq -c | sort -rn
echo "--- source-origin occurrences without an artifact (the population gap) ---"
jq -r '.queries[] | select(.family=="batch") | .occurrences[]
       | select(.origin.kind=="source" and .artifact==null)
       | "\(.role) \(.emission.kind // "-")"' "$OUT/vstd.json" | sort | uniq -c | sort -rn
echo "--- declared fallback citations (must all be absent) ---"
jq -r '.queries[].occurrences[] | .rule // empty, .join_rule // empty' "$OUT/vstd.json" \
  | grep -E "order_alignment|signature_bucket|const_false_exclusion|loop_inv_ordinal|requires_index" \
  | sort | uniq -c || echo "  none"
