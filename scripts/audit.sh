#!/usr/bin/env bash
# Scan Lean sources for forbidden constructs and remaining sorries.
# usage: bash scripts/audit.sh
# The definitive check is the `#print axioms` line at the end of Zeta2Lean/Main.lean (printed by
# `bash scripts/build.sh Zeta2Lean`): it must list only propext, Classical.choice, Quot.sound
# (plus sorryAx while stubs remain).  This grep is a fast census; it also catches declarations
# hidden behind modifiers/attributes (`private axiom`, `@[simp] axiom`, `noncomputable opaque`, ...).
cd "$(dirname "$0")/.." || exit 2
echo "== sorry / admit per file"
grep -rcE '\b(sorry|admit)\b' --include='*.lean' Zeta2Lean | grep -v ':0$' || echo "(none)"
echo "== forbidden constructs (axiom/opaque/unsafe declarations, also after modifiers or attributes; native_decide, implemented_by, extern, debug.skipKernelTC, ofReduceBool, trustCompiler)"
grep -rnE '^\s*(@\[[^]]*\]\s*)*((private|protected|noncomputable|partial|nonrec|scoped|local|unsafe)\s+)*(axiom|opaque|unsafe)\b|native_decide|implemented_by|@\[extern|debug\.skipKernelTC|Lean\.ofReduceBool|Lean\.trustCompiler' --include='*.lean' Zeta2Lean || echo "(none)"
