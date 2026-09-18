#!/usr/bin/env bash
# Regression: the lowering sidecar must report the emitting template slot and
# the declaring clause ordinal, and the ordinal must index the *declaring*
# invariant list rather than a projection of it.
#
# `three_clause_shapes` declares, in order:
#   [0] invariant_except_break   at_entry only
#   [1] invariant                at_entry AND at_exit  -> pushed into BOTH
#   [2] ensures                  at_exit only
# so the entry slots must see {0,1} and the exit slots must see {1,2}.
# A projection index would report {0,1} for the exit slots instead, silently
# attributing `invariant` to `invariant_except_break`.
set -euo pipefail
cd "$(dirname "$0")/.." # source/
V=${PC_VERUS:-./target-verus/release/verus}
U=${PC_AUDIT:-./target-verus/release/pc_audit}
OUT=$(mktemp "${TMPDIR:-/tmp}/proof-coverage-slots.XXXXXX.json")
trap 'rm -f "$OUT"' EXIT

timeout 180 env VERUS_PROOF_COVERAGE_OUT="$OUT" \
  "$V" proof_coverage/probes/emission_slots.rs -V proof-coverage --crate-type=lib >/dev/null
"$U" "$OUT" >/dev/null

# clauses seen at a given loop protocol point (the typed emission role), as a
# sorted ordinal list
clauses() {
  jq -r --arg point "$1" '
    [ .queries[]
      | select((.fun // "") | test("three_clause_shapes"))
      | .occurrences[]
      | select(.emission.kind == "loop_invariant" and .emission.point == $point
               and (.artifact // "" | test("#inv\\.src[0-9]+$")))
      | .artifact | sub(".*#inv\\.src";"") | tonumber
    ] | unique | @csv' "$OUT"
}
expect() { # point expected actual
  [ "$3" = "$2" ] || { echo "SLOT DRIFT: $1 expected {$2} got {$3}"; exit 1; }
}
expect establish  '0,1' "$(clauses establish)"
expect body_entry '0,1' "$(clauses body_entry)"
expect maintain   '0,1' "$(clauses maintain)"
expect exit       '1,2' "$(clauses exit)"
expect transfer   '1,2' "$(clauses transfer)"

# Every loop-clause occurrence must reach its clause by construction, never by
# span or ordinal inference.
inferred=$(jq -r '[ .queries[] | .occurrences[]
  | select((.origin.detail // "") == "loop_invariant")
  | select((.join_rule // "") | test("clause_span|loop_inv_ordinal")) ] | length' "$OUT")
[ "$inferred" = "0" ] || { echo "SLOT DRIFT: $inferred loop clauses still joined by inference"; exit 1; }

# The positional slot-reconstruction rules must not fire on this probe.
positional=$(jq -r '[ .queries[] | .occurrences[]
  | select((.rule // "") | test("^walk\\.loop|^walk\\.branch")) ] | length' "$OUT")
[ "$positional" = "0" ] || { echo "SLOT DRIFT: $positional positional loop/branch rules fired"; exit 1; }

echo "emission slots exact"
