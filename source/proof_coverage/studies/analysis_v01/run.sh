#!/usr/bin/env bash
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
SOURCE=$(cd "$HERE/../../.." && pwd)
OUT=${1:-"$HERE/out"}
VERUS=${PC_VERUS:-"$SOURCE/target-verus/release/verus"}
AUDIT=${PC_AUDIT:-"$SOURCE/target-verus/release/pc_audit"}
ANALYZE=${PC_ANALYZE:-"$SOURCE/target-verus/release/pc_analyze"}

mkdir -p "$OUT"

run_example() {
    local example=$1
    local function=$2
    local example_out="$OUT/$example"
    mkdir -p "$example_out"

    (
        cd "$SOURCE"
        env VERUS_PROOF_COVERAGE_OUT="$example_out/record.json" \
            "$VERUS" "proof_coverage/studies/analysis_v01/$example.rs" \
            -V proof-coverage
    ) >"$example_out/verus.log"
    "$AUDIT" "$example_out/record.json" >"$example_out/audit.txt"
    "$ANALYZE" "$example_out/record.json" study "$function" opaque \
        >"$example_out/findings.txt"
}

# Like run_example, but the research view expands calls (interprocedural).
run_example_modular() {
    local example=$1
    local function=$2
    local example_out="$OUT/$example"
    mkdir -p "$example_out"

    (
        cd "$SOURCE"
        env VERUS_PROOF_COVERAGE_OUT="$example_out/record.json" \
            "$VERUS" "proof_coverage/studies/analysis_v01/$example.rs" \
            -V proof-coverage
    ) >"$example_out/verus.log"
    "$AUDIT" "$example_out/record.json" >"$example_out/audit.txt"
    "$ANALYZE" "$example_out/record.json" study "$function" modular \
        >"$example_out/findings.txt"
}

# Two crates: crate_b calls crate_a. Both records are analyzed together; the
# modular slice of crate_b's function must cross into crate_a's proof.
run_crates() {
    local crates_out="$OUT/crates"
    mkdir -p "$crates_out"
    (
        cd "$crates_out"
        env VERUS_PROOF_COVERAGE_OUT="$crates_out/a.json" \
            "$VERUS" "$HERE/crates/crate_a.rs" --crate-type=lib \
            --export crate_a.vir --compile -o libcrate_a.rlib -V proof-coverage
        env VERUS_PROOF_COVERAGE_OUT="$crates_out/b.json" \
            "$VERUS" "$HERE/crates/crate_b.rs" \
            --extern crate_a=libcrate_a.rlib --import crate_a=crate_a.vir -V proof-coverage
    ) >"$crates_out/verus.log"
    "$AUDIT" "$crates_out/a.json" "$crates_out/b.json" >"$crates_out/audit.txt"
    "$ANALYZE" "$crates_out/a.json" "$crates_out/b.json" study twice modular \
        >"$crates_out/findings.txt"
    "$ANALYZE" "$crates_out/a.json" "$crates_out/b.json" \
        impact 'r0%crate_a::add_one#ens[1]' modular >"$crates_out/impact.txt"
}

run_example joint joint_chain
run_example vacuity contradictory
run_example loop_isolation count_to
run_example nested nested_count
run_example recursion recursion
run_example trait_boundary use_increment
run_example established established
run_example auxiliary abs_like
run_example ambient uses_ambient
run_example models all_positive
run_example mutation mutation
run_example_modular traits_modular traits_modular
run_crates

cat \
    "$OUT/joint/findings.txt" \
    "$OUT/vacuity/findings.txt" \
    "$OUT/loop_isolation/findings.txt" \
    "$OUT/nested/findings.txt" \
    "$OUT/recursion/findings.txt" \
    "$OUT/trait_boundary/findings.txt" \
    "$OUT/established/findings.txt" \
    "$OUT/auxiliary/findings.txt" \
    "$OUT/ambient/findings.txt" \
    "$OUT/models/findings.txt" \
    "$OUT/mutation/findings.txt" \
    "$OUT/traits_modular/findings.txt" \
    "$OUT/crates/findings.txt" \
    "$OUT/crates/impact.txt" \
    >"$OUT/findings.txt"

echo "analysis v0.1 study written to $OUT"
