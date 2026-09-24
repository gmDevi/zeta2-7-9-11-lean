#!/usr/bin/env bash
# Elaborate ONE Lean file against the already-built imports (writes no .olean, safe to run in parallel).
# usage (from the project root):
#   bash scripts/check.sh Zeta2Lean/Proofs/Foo.lean
# env: TIMEOUT (seconds, default 1800)
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.." || exit 2
f="$1"
if [ ! -f "$f" ]; then echo "no such file: $f"; exit 2; fi
start=$(date +%s)
timeout "${TIMEOUT:-1800}" lake env lean "$f" > "/tmp/check.$$.log" 2>&1
code=$?
end=$(date +%s)
head -c 150000 "/tmp/check.$$.log"
rm -f "/tmp/check.$$.log"
echo "---"
echo "exit=$code  seconds=$((end-start))  sorry_count=$(grep -c '\bsorry\b' "$f")"
