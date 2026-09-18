#!/usr/bin/env bash
# Generate one inspectable findings report over a set of examples.
#
# Usage:
#   ./proof_coverage/findings_report.sh [OUTDIR] [FILE.rs ...]
#
# With no files, runs the curated set below. Each example has an explicit
# expected signal, so the driver fails if a demonstration silently stops
# exercising the finding it was selected for. Each example is verified with
# coverage, audited, rendered, and concatenated into REPORT.md with an index.
#
# The report quotes the source it names, so it can be read — by a person or an
# agent — without opening the examples.
set -uo pipefail
cd "$(dirname "$0")/.."   # source/

OUT=${1:-/tmp/proof-coverage-findings}
shift || true
V=./target-verus/release/verus
A=./target-verus/release/pc_analyze
U=./target-verus/release/pc_audit

if [[ ! -x "$V" || ! -x "$A" || ! -x "$U" ]]; then
    echo "missing release binaries; build Verus and proof_coverage first" >&2
    exit 2
fi
if ! command -v jq >/dev/null 2>&1; then
    echo "missing jq; structured report counts and signal checks require it" >&2
    exit 2
fi

# Curated set. Each entry is chosen for a specific finding family:
#
#   guide/quants.rs        goal-unused-precondition, including a duplicated
#                          `requires` in Verus's own tutorial
#   vectors.rs             auxiliary-only proof and implementation facts
#   rw2022_script.rs       a dead loop invariant, ablation-confirmed
#   summer_school/chapter-2-3.rs
#                          vacuous-postcondition extent=all — an `assume(false)`
#                          stub whose contract is not proved at all
#   broadcast_proof.rs     trusted-dependency: `admit()` standing in for a
#                          commented-out `by (integer_ring)` proof
#   cuckoo_hash_table/rwlock.rs
#                          unobserved-context, ablation-confirmed
#   atomic_increment.rs    WITHHELD rows: the atomic-update protocol has no
#                          licensing rule, so absence claims here are not
#                          defensible (PROOF_COVERAGE_GAPS.md §4.1)
#   guide/references.rs    a small mixed case
CURATED=(
    ../examples/guide/quants.rs
    ../examples/vectors.rs
    ../examples/rw2022_script.rs
    ../examples/summer_school/chapter-2-3.rs
    ../examples/broadcast_proof.rs
    ../examples/cuckoo_hash_table/rwlock.rs
    ../examples/atomic_increment.rs
    ../examples/guide/references.rs
)

declare -A EXPECTED_KIND=(
    [guide__quants]=goal-unused-precondition
    [vectors]=auxiliary-only-fact
    [rw2022_script]=checked-but-unused-proof-step
    [summer_school__chapter-2-3]=vacuous-postcondition
    [broadcast_proof]=trusted-dependency
    [cuckoo_hash_table__rwlock]=unobserved-context
    [guide__references]=checked-but-unused-proof-step
)

if [[ $# -gt 0 ]]; then FILES=("$@"); else FILES=("${CURATED[@]}"); fi

mkdir -p "$OUT"
REPORT="$OUT/REPORT.md"
: > "$REPORT"
{
    echo "# Proof-coverage findings"
    echo
    echo "Generated $(date -u +%Y-%m-%dT%H:%M:%SZ) by \`proof_coverage/findings_report.sh\`."
    echo
    echo "Vocabulary: \`PROOF_COVERAGE_FINDINGS.md\` §2. A finding is"
    echo "witness-relative and root-relative: core absence is not removability"
    echo "(§1, §4). Rows marked \`[WH]\` are **withheld** — their root evidence is"
    echo "incomplete or source attribution is occluded, so a supporting fact may"
    echo "have dropped out and the row must not be acted on."
    echo
    echo "| example | verified | review | trust subjects | secondary | withheld |"
    echo "|---|---|---:|---:|---:|---:|"
} >> "$REPORT"

declare -a BODIES=()
fail=0

for src in "${FILES[@]}"; do
    name=$(basename "$src" .rs)
    slug=$(echo "${src#../examples/}" | sed 's|/|__|g; s|\.rs$||')
    rec="$OUT/$slug.json"
    report_json="$OUT/$slug.report.json"
    log="$OUT/$slug.verus.log"

    # `--crate-type=lib` so examples without `fn main` still verify.
    if ! timeout 600 env VERUS_PROOF_COVERAGE_OUT="$rec" \
        "$V" --crate-type=lib "$src" -V proof-coverage > "$log" 2>&1; then
        verdict="VERIFY FAILED"
        echo "| \`${src#../}\` | **$verdict** | — | — | — | — |" >> "$REPORT"
        BODIES+=("$OUT/$slug.txt")
        { echo "## ${src#../}"; echo; echo '```'; tail -20 "$log"; echo '```'; } \
            > "$OUT/$slug.txt"
        fail=1
        continue
    fi
    verdict=$(grep -oE "[0-9]+ verified, [0-9]+ errors" "$log" | tail -1)

    if ! "$U" "$rec" > "$OUT/$slug.audit.txt" 2>&1; then
        echo "  audit failed for $src" >&2
        echo "| \`${src#../}\` | **AUDIT FAILED** | — | — | — | — |" >> "$REPORT"
        BODIES+=("$OUT/$slug.txt")
        { echo "## ${src#../}"; echo; echo '```'; tail -40 "$OUT/$slug.audit.txt"; echo '```'; } \
            > "$OUT/$slug.txt"
        fail=1
        continue
    fi

    if ! "$A" "$rec" report opaque > "$report_json" 2> "$OUT/$slug.report.err"; then
        echo "  report generation failed for $src" >&2
        echo "| \`${src#../}\` | **REPORT FAILED** | — | — | — | — |" >> "$REPORT"
        BODIES+=("$OUT/$slug.txt")
        { echo "## ${src#../}"; echo; echo '```'; cat "$OUT/$slug.report.err"; echo '```'; } \
            > "$OUT/$slug.txt"
        fail=1
        continue
    fi
    if ! "$A" "$rec" findings opaque > "$OUT/$slug.findings.txt" 2>&1; then
        echo "  findings rendering failed for $src" >&2
        echo "| \`${src#../}\` | **RENDER FAILED** | — | — | — | — |" >> "$REPORT"
        BODIES+=("$OUT/$slug.txt")
        { echo "## ${src#../}"; echo; echo '```'; cat "$OUT/$slug.findings.txt"; echo '```'; } \
            > "$OUT/$slug.txt"
        fail=1
        continue
    fi

    review=$(jq '[.functions[]?.findings[]?
        | select(.claim != "trust" and .defensible != false)] | length' "$report_json")
    trust=$(jq '[.functions[]?.findings[]? | select(.claim == "trust") | .subject]
        | unique | length' "$report_json")
    secondary=$(jq '[.functions[]?.secondary_observations[]?] | length' "$report_json")
    w=$(jq '[.functions[]?.findings[]? | select(.defensible == false)] | length' "$report_json")
    echo "| \`${src#../}\` | $verdict | $review | $trust | $secondary | $w |" >> "$REPORT"

    if [[ -n "${EXPECTED_KIND[$slug]:-}" ]] \
        && ! jq -e --arg kind "${EXPECTED_KIND[$slug]}" \
            'any(.functions[]?.findings[]?; .kind == $kind)' "$report_json" >/dev/null; then
        echo "  expected ${EXPECTED_KIND[$slug]} missing for $src" >&2
        fail=1
    fi
    if [[ "$slug" == atomic_increment ]] \
        && ! jq -e 'any(.functions[]?.findings[]?; .defensible == false)' \
            "$report_json" >/dev/null; then
        echo "  expected withheld finding missing for $src" >&2
        fail=1
    fi

    { echo "## ${src#../}"; echo; echo '```text';
      cat "$OUT/$slug.findings.txt"; echo '```'; } > "$OUT/$slug.txt"
    BODIES+=("$OUT/$slug.txt")
done

{
    echo
    echo "Records, per-example reports and audits are beside this file in \`$OUT\`."
    echo
    for body in "${BODIES[@]}"; do echo; cat "$body"; done
} >> "$REPORT"

echo "report: $REPORT"
[ "$fail" = 0 ] \
    || echo "note: at least one verification, audit, report, render, or signal check failed" >&2
exit "$fail"
