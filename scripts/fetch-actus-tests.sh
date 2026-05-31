#!/usr/bin/env bash
# Fetch the ACTUS Foundation reference test cases used by the conformance
# harness (`lake exe conformance`).  These files are not committed; run this
# once locally or in CI before `lake exe conformance`.
set -euo pipefail

dir="${1:-actus-tests}"
base="https://raw.githubusercontent.com/actusfrf/actus-tests/master/tests"

mkdir -p "$dir"
for c in pam lam nam ann clm swaps com stk optns; do
  curl -fsSL -o "$dir/actus-tests-$c.json" "$base/actus-tests-$c.json"
  echo "fetched $dir/actus-tests-$c.json"
done
