#!/usr/bin/env bash
# Regression fixtures: check the five frozen explanation traces and
# call-local induction notes. Set UPDATE_FIXTURES=1 to regenerate them.
# Source findings use the typed report contract and are checked by
# proof_coverage/demo instead of a second legacy engine.
set -u
cd "$(dirname "$0")/../.."   # source/
V=./target-verus/release/verus
A=./target-verus/release/pc_analyze
P=proof_coverage/probes
F=proof_coverage/fixtures
T=$(mktemp -d)
fail=0
run() { timeout 120 env VERUS_PROOF_COVERAGE_OUT="$2" $V "$1" -V proof-coverage >/dev/null 2>&1; }
run $P/nested_loops.rs $T/nested.json
run $P/traits.rs $T/traits.json
run $P/call_residue.rs $T/residue.json
run $P/recursion_contracts.rs $T/rc.json
check() { # record target fixture
  $A "$1" explain "$2" | sed "s|$(pwd)/||g; s|/local/home/[^ ]*/proof-coverage-artifact/verus/||g; s|$T/||g" > "$T/out.trace"
  if [ "${UPDATE_FIXTURES:-0}" = 1 ]; then
    cp "$T/out.trace" "$3"
    return
  fi
  if ! diff -u "$3" "$T/out.trace" > "$T/d"; then
    echo "FIXTURE DRIFT: $3"; head -6 "$T/d"; fail=1
  fi
}
check $T/nested.json  "pc%18%13" $F/nested_postcondition.trace
check $T/traits.json  "pc%8%21"  $F/lemma_chain.trace
check $T/residue.json "pc%3%1"   $F/ordinary_call.trace
check $T/rc.json      "pc%6%7"   $F/certified_recursion.trace
check $T/rc.json      "pc%18%6"  $F/unguarded_recursion.trace
$A $T/rc.json summary | grep induction > "$T/notes"
if [ "${UPDATE_FIXTURES:-0}" = 1 ]; then
  cp "$T/notes" "$F/induction_notes.txt"
elif ! diff -q $F/induction_notes.txt "$T/notes" >/dev/null; then
  echo "FIXTURE DRIFT: induction_notes"
  fail=1
fi
[ -n "${KEEP_T:-}" ] && echo "kept $T" || rm -rf "$T"
[ $fail -eq 0 ] && {
  [ "${UPDATE_FIXTURES:-0}" = 1 ] && echo "fixtures updated" || echo "all fixtures match"
}
exit $fail
