#!/usr/bin/env bash
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
OUT=$(mktemp -d "${TMPDIR:-/tmp}/proof-coverage-demo.XXXXXX")
trap 'rm -rf "$OUT"' EXIT

"$HERE/run.sh" "$OUT" >/dev/null
diff -u "$HERE/expected-findings.json" "$OUT/findings.json"
echo "query findings demo matches"
