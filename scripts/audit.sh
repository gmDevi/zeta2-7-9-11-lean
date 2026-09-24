#!/usr/bin/env bash
# Scan Lean sources for forbidden constructs and remaining sorries.
# usage: wsl -d Ubuntu --cd /home/mdevi/zeta2-lean -- bash scripts/audit.sh
cd "$HOME/zeta2-lean" || exit 2
echo "== sorry / admit per file"
grep -rcE '\b(sorry|admit)\b' --include='*.lean' Zeta2Lean | grep -v ':0$' || echo "(none)"
echo "== forbidden constructs (axiom, native_decide, implemented_by, extern, unsafe, opaque, set_option debug.skipKernelTC)"
grep -rnE '^\s*(axiom|unsafe|opaque)\b|native_decide|implemented_by|@\[extern|debug\.skipKernelTC|Lean\.ofReduceBool' --include='*.lean' Zeta2Lean || echo "(none)"
