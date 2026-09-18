#!/usr/bin/env bash
# Run the smallest end-to-end proof-coverage study.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
SOURCE=$(cd "$HERE/../.." && pwd)
OUT=${1:-"$HERE/out"}
VERUS=${PC_VERUS:-"$SOURCE/target-verus/release/verus"}
AUDIT=${PC_AUDIT:-"$SOURCE/target-verus/release/pc_audit"}
ANALYZE=${PC_ANALYZE:-"$SOURCE/target-verus/release/pc_analyze"}

mkdir -p "$OUT"

env VERUS_PROOF_COVERAGE_OUT="$OUT/record.json" \
  "$VERUS" "$HERE/query_findings.rs" -V proof-coverage
"$AUDIT" "$OUT/record.json"
"$ANALYZE" "$OUT/record.json" report opaque > "$OUT/report.json"

jq '
  # Findings carry the PROOF_COVERAGE_FINDINGS.md §2 vocabulary: `kind` is the
  # subtype, `claim` is what sort of statement it makes, and `defensible` is
  # false when the slice rests on an unlicensed exported assumption.
  def compact:
    {
      kind,
      claim,
      defensible,
      source_artifact: (.source.artifact // .subject // .function),
      source_kind: .source.artifact_kind,
      terminal_artifacts: (
        if .terminals then ([.terminals[].artifact] | unique)
        elif .terminal then [.terminal.artifact]
        else [] end
      ),
      terminal_kinds: (
        if .terminals then ([.terminals[].artifact_kind] | unique)
        elif .terminal then [.terminal.artifact_kind]
        else [] end
      )
    };
  {
    # Query scope holds observations, not findings: one row per (fact,
    # terminal). Summing them across queries is meaningless.
    observation: [
      .query_observations[]
      | (compact + { functions: [.terminal.function] })
      | del(.claim, .defensible)
    ] | sort_by(.kind, .functions, .source_artifact),
    function: [
      .functions[]
      | .function as $fn
      | .findings[]
      | compact + { functions: [$fn] }
    ] | sort_by(.kind, .functions, .source_artifact),
    file: [
      .files[]
      | .file as $file
      | .findings[]
      | {
          file: ($file | split("/") | last),
          finding: compact
        }
    ] | sort_by(.file, .finding.kind, .finding.source_artifact)
  }
' "$OUT/report.json" > "$OUT/findings.json"

echo
echo "Proof-coverage findings"
jq -r '
  ["observation", "function", "file"][] as $level
  | "  \($level):",
    (.[$level][]
      | if $level == "file" then .finding else . end
      | "    \(.kind)\(if .defensible == false then " (withheld)" else "" end)  \(.source_artifact)")
' "$OUT/findings.json"
echo
echo "Record:   $OUT/record.json"
echo "Report:   $OUT/report.json"
echo "Findings: $OUT/findings.json"
