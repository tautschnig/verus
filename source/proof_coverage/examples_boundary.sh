#!/usr/bin/env bash
# Compare ordinary Verus and proof-coverage runs over examples/.
#
# This is an evaluation harness, not a pass/fail probe sweep.  Expected
# verification failures are retained as data.  The hard failure classes are:
# canonical-result/diagnostic drift, missing records for successful proofs,
# batch-shadow disagreement, and record-audit violations. Failed focused
# queries are reported as opaque measurements and do not fail the run.
set -u

SOURCE_DIR="$(cd "$(dirname "$0")/.." && pwd)"
REPO_DIR="$(cd "$SOURCE_DIR/.." && pwd)"
PROFILE="${PC_PROFILE:-release}"
TARGET="$SOURCE_DIR/target-verus/$PROFILE"
VERUS="$TARGET/rust_verify"
AUDIT="$TARGET/pc_audit"
ANALYZE="$TARGET/pc_analyze"
OUT_DIR="${PC_BOUNDARY_OUT:-/tmp/proof-coverage-examples}"
RUN_TIMEOUT="${PC_BOUNDARY_TIMEOUT:-600}"
INCLUDE_SINGULAR="${PC_INCLUDE_SINGULAR:-0}"
RUSTC_LIBDIR="$(rustc --print sysroot)/lib"
RUN_LD_LIBRARY_PATH="$RUSTC_LIBDIR${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

if [[ ! -x "$VERUS" || ! -x "$AUDIT" || ! -x "$ANALYZE" ]]; then
    echo "missing $PROFILE binaries; build Verus and proof_coverage first" >&2
    exit 2
fi

mkdir -p "$OUT_DIR"
RESULTS="$OUT_DIR/results.tsv"
printf '%s\n' \
    $'file\tmode\tbaseline\tcoverage\texecution\tbaseline_ms\tcoverage_ms\tverdict_invariant\tdiagnostics_invariant\trecord\taudit\tcanonical_unproved_batches\tbatch_integrity_failures\tbatch_opaque\tfocused_opaque\tcore_primary\tcore_fallback\tunresolved_premises\tunresolved_obligations\tcanonicalization\tintraprocedural_report\tquery_overapproximated\tfunction_overapproximated\tfunction_ungrounded' \
    > "$RESULTS"
hard_fail=0

if [[ $# -gt 0 ]]; then
    files=("$@")
else
    mapfile -d '' files < <(find "$REPO_DIR/examples" -type f -name '*.rs' -print0 | sort -z)
fi

run_one() {
    local file="$1"
    if [[ "$file" != /* ]]; then
        if [[ -f "$file" ]]; then
            file="$(cd "$(dirname "$file")" && pwd)/$(basename "$file")"
        else
            file="$REPO_DIR/$file"
        fi
    fi
    if [[ ! -f "$file" ]]; then
        echo "missing example: $1" >&2
        return 2
    fi
    local rel="${file#"$REPO_DIR/"}"
    local first
    first="$(head -n 1 "$file")"
    local mode="expect-success"
    local -a example_args=()
    case "$first" in
        *" ignore"*)
            printf '%s\n' "$rel	skip	skip	skip	not-run	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-" >> "$RESULTS"
            echo "SKIP  $rel"
            return
            ;;
        *"expect-errors"*)
            mode="expect-errors"
            ;;
        *"expect-failures"*|*"expand-errors"*)
            mode="expect-failures"
            ;;
        *"expect-warnings"*)
            mode="expect-warnings"
            ;;
    esac
    if [[ "$first" == *"expand-errors"* ]]; then
        example_args+=(--expand-errors)
    fi
    if [[ "$first" == *"no-report-long-running"* ]]; then
        example_args+=(--no-report-long-running)
    fi
    if [[ "$rel" == examples/integer_ring/* && "$INCLUDE_SINGULAR" != 1 ]]; then
        printf '%s\n' \
            "$rel	requires-singular	not-run	not-run	not-run	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-	-" \
            >> "$RESULTS"
        echo "SKIP  $rel  (requires a --features singular build; set PC_INCLUDE_SINGULAR=1)"
        return
    fi

    local slug="${rel//\//__}"
    slug="${slug%.rs}"
    local base_stdout="$OUT_DIR/$slug.base.stdout"
    local base_stderr="$OUT_DIR/$slug.base.stderr"
    local cov_stdout="$OUT_DIR/$slug.coverage.stdout"
    local cov_stderr="$OUT_DIR/$slug.coverage.stderr"
    local record="$OUT_DIR/$slug.json"
    local base_meta="$OUT_DIR/$slug.base.rmeta"
    local cov_meta="$OUT_DIR/$slug.coverage.rmeta"

    local -a common=(
        --internal-test-mode
        --crate-name test_crate
        --crate-type lib
        --extern "verus_builtin=$TARGET/libverus_builtin.rlib"
        --extern "verus_builtin_macros=$TARGET/libverus_builtin_macros.so"
        --extern "verus_state_machines_macros=$TARGET/libverus_state_machines_macros.so"
        -L "dependency=$TARGET"
        -Z write_long_types_to_disk=no
        -A non_snake_case
        -A deprecated
        --emit=metadata
        --cfg vstd_todo
        --extern "vstd=$TARGET/libvstd.rlib"
        --import "vstd=$TARGET/vstd.vir"
    )

    local base_start base_ms
    base_start="$(date +%s%3N)"
    timeout "$RUN_TIMEOUT" env LD_LIBRARY_PATH="$RUN_LD_LIBRARY_PATH" \
        VERUS_Z3_PATH="$SOURCE_DIR/z3" \
        "$VERUS" "${common[@]}" "${example_args[@]}" -o "$base_meta" "$file" \
        >"$base_stdout" 2>"$base_stderr"
    local base_rc=$?
    base_ms=$(( $(date +%s%3N) - base_start ))

    local cov_start cov_ms
    cov_start="$(date +%s%3N)"
    local -a coverage_env=(
        "LD_LIBRARY_PATH=$RUN_LD_LIBRARY_PATH"
        "VERUS_Z3_PATH=$SOURCE_DIR/z3"
        "VERUS_PROOF_COVERAGE_OUT=$record"
    )
    timeout "$RUN_TIMEOUT" env "${coverage_env[@]}" \
        "$VERUS" "${common[@]}" "${example_args[@]}" -V proof-coverage \
        -o "$cov_meta" "$file" >"$cov_stdout" 2>"$cov_stderr"
    local cov_rc=$?
    cov_ms=$(( $(date +%s%3N) - cov_start ))

    local base_result cov_result
    base_result="$(sed -n 's/^verification results:: //p' "$base_stdout" | tail -n 1)"
    cov_result="$(sed -n 's/^verification results:: //p' "$cov_stdout" | tail -n 1)"
    local execution="complete"
    if [[ "$base_rc" -eq 124 && "$cov_rc" -eq 124 ]]; then
        execution="both-timeout"
    elif [[ "$base_rc" -eq 124 ]]; then
        execution="baseline-timeout"
    elif [[ "$cov_rc" -eq 124 ]]; then
        execution="coverage-timeout"
    fi
    local invariant="yes"
    if [[ "$execution" != "complete" ]]; then
        invariant="unknown"
        hard_fail=1
    elif [[ "$base_result" != "$cov_result" || "$base_rc" -ne "$cov_rc" ]]; then
        invariant="NO"
        hard_fail=1
    fi
    local base_diag="$OUT_DIR/$slug.base.normalized.stderr"
    local cov_diag="$OUT_DIR/$slug.coverage.normalized.stderr"
    cp "$base_stderr" "$base_diag"
    sed \
        -e '/^proof-coverage:/d' \
        -e '/^verification observer failed /d' \
        "$cov_stderr" > "$cov_diag"
    local diagnostics_invariant="yes"
    if ! cmp -s "$base_diag" "$cov_diag"; then
        diagnostics_invariant="NO"
        hard_fail=1
    elif [[ "$execution" != "complete" ]]; then
        diagnostics_invariant="observed-equal"
    fi
    local successful_proof=0
    if [[ "$base_rc" -eq 0 && "$base_result" == *"0 errors"* ]]; then
        successful_proof=1
    fi
    [[ -n "$base_result" ]] || base_result="rc=$base_rc"
    [[ -n "$cov_result" ]] || cov_result="rc=$cov_rc"

    local record_state="missing"
    local audit_state="-"
    local canonical_unproved="-"
    local batch_integrity="-"
    local batch_opaque="-"
    local focused_opaque="-"
    local core_primary="-"
    local core_fallback="-"
    local unresolved_premises="-"
    local unresolved_obligations="-"
    local report_state="-"
    local query_overapproximated="-"
    local function_overapproximated="-"
    local function_ungrounded="-"
    if [[ -s "$record" ]]; then
        record_state="present"
        if "$AUDIT" "$record" >"$OUT_DIR/$slug.audit.stdout" \
            2>"$OUT_DIR/$slug.audit.stderr"; then
            audit_state="clean"
        else
            audit_state="VIOLATION"
            hard_fail=1
        fi
        canonical_unproved="$(jq '[.queries[] | select(
            .family == "batch"
            and ((.shadow_result // "") | startswith("canonical_"))
        )] | length' "$record")"
        batch_integrity="$(jq '[.queries[] | select(
            .family == "batch"
            and (.shadow_result == "invalid"
                 or .shadow_result == "type_error"
                 or .shadow_result == "unexpected_output"
                 or .shadow_result == "proof_fallback_invalid"
                 or .shadow_result == "proof_fallback_type_error"
                 or .shadow_result == "proof_fallback_unexpected_output")
        )] | length' "$record")"
        batch_opaque="$(jq '[.queries[] | select(
            .family == "batch"
            and .shadow_result != "valid"
            and (((.shadow_result // "") | startswith("canonical_")) | not)
            and (.shadow_result != "invalid")
            and (.shadow_result != "type_error")
            and (.shadow_result != "unexpected_output")
            and (.shadow_result != "proof_fallback_invalid")
            and (.shadow_result != "proof_fallback_type_error")
            and (.shadow_result != "proof_fallback_unexpected_output")
        )] | length' "$record")"
        focused_opaque="$(jq '[.queries[] | select(
            .family == "focused"
            and .shadow_result != "valid"
            and (((.shadow_result // "") | startswith("canonical_")) | not)
        )] | length' "$record")"
        core_primary="$(jq '[.queries[] | select(.evidence_backend == "unsat_core")] | length' "$record")"
        core_fallback="$(jq '[.queries[] | select(
            .evidence_backend == "proof_enabled_unsat_core"
        )] | length' "$record")"
        unresolved_premises="$(jq '.summary.unresolved_premises' "$record")"
        unresolved_obligations="$(jq '.summary.unresolved_obligations' "$record")"
        if [[ "$batch_integrity" -ne 0 ]]; then
            hard_fail=1
        fi
        local intraprocedural_report="$OUT_DIR/$slug.intraprocedural.json"
        local modular_report="$OUT_DIR/$slug.modular.json"
        if "$ANALYZE" "$record" report opaque >"$intraprocedural_report" \
            2>"$OUT_DIR/$slug.intraprocedural.stderr" \
            && "$ANALYZE" "$record" report modular >"$modular_report" \
                2>"$OUT_DIR/$slug.modular.stderr"; then
            report_state="present"
            query_overapproximated="$(jq '[.queries[] | select(
                .status == "Overapproximated"
            )] | length' "$intraprocedural_report")"
            function_overapproximated="$(jq '[.functions[] | select(
                .status == "Overapproximated"
            )] | length' "$intraprocedural_report")"
            function_ungrounded="$(jq '[.functions[] | select(
                .status == "Ungrounded"
            )] | length' "$intraprocedural_report")"
        else
            report_state="FAILED"
            hard_fail=1
        fi
    elif [[ "$successful_proof" -eq 1 && "$execution" == "complete" ]]; then
        hard_fail=1
    fi

    local canonicalization="-"
    if [[ "$record_state" == "present" ]]; then
        canonicalization="canonical"
        if rg -q 'canonicalization refused' "$cov_stderr"; then
            canonicalization="refused"
        fi
    fi

    printf '%s\n' \
        "$rel	$mode	$base_result	$cov_result	$execution	$base_ms	$cov_ms	$invariant	$diagnostics_invariant	$record_state	$audit_state	$canonical_unproved	$batch_integrity	$batch_opaque	$focused_opaque	$core_primary	$core_fallback	$unresolved_premises	$unresolved_obligations	$canonicalization	$report_state	$query_overapproximated	$function_overapproximated	$function_ungrounded" \
        >> "$RESULTS"
    echo "$execution $invariant/$diagnostics_invariant  $rel  base=[$base_result] coverage=[$cov_result] time=${base_ms}/${cov_ms}ms audit=$audit_state canonical-unproved=$canonical_unproved integrity=$batch_integrity opaque=$batch_opaque/$focused_opaque"
}

for file in "${files[@]}"; do
    run_one "$file"
done

echo "results: $RESULTS"
exit "$hard_fail"
