#!/usr/bin/env bash
# Observe how each clause occurrence is attributed to a source clause.
#
# Usage: observe_slots.sh RECORD.json [FUNCTION_SUBSTRING]
#
# Prints one row per occurrence that carries or should carry a source clause
# identity, showing the mechanism that produced the attribution. Used to
# compare attribution before and after the emission-slot change: the artifact
# column must not change, and the mechanism column must move from inference
# (join.clause_span, join.loop_inv_ordinal, walk.*) to exact provenance.
set -euo pipefail

record=${1:?usage: observe_slots.sh RECORD.json [FUNCTION_SUBSTRING]}
filter=${2:-}

jq -r --arg filter "$filter" '
  def short: if . == null then "-" else (. | sub(".*emission_slots\\.rs:"; "L") | sub(":.*"; "")) end;
  def art:   if . == null then "NONE" else (. | sub(".*::"; "")) end;
  .queries[]
  | select(($filter == "") or ((.fun // "") | test($filter)))
  | (.fun // "?" | sub(".*::"; "")) as $fn
  | .occurrences[]?
  | select((.origin.detail // "") | test("invariant|ensures|require|assert|branch|loop|proposition"))
  | [ $fn,
      ((.emission // {}) | [.kind, .point, .site, .at, .section, .arm] | map(select(. != null) | tostring) | join(".") | if . == "" then "-" else . end),
      (.role),
      (.origin.detail),
      (.rule),
      (.join_rule // "-"),
      (.artifact | art),
      (.span | short)
    ] | @tsv
' "$record" | sort | awk -F'\t' '
BEGIN {
  printf "%-22s %-22s %-8s %-22s %-26s %-20s %-26s %s\n", \
         "FUNCTION","PHASE","ROLE","ORIGIN","RULE (site)","JOIN (artifact)","ARTIFACT","LINE"
  printf "%s\n", "-------------------------------------------------------------------------------------------------------------------------------------------------------------"
}
{ printf "%-22s %-22s %-8s %-22s %-26s %-20s %-26s %s\n", $1,$2,$3,$4,$5,$6,$7,$8 }
'
