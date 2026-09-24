/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib

/-!
# Compactly supported functions are dense in Schwartz space (VENDORED — currently a stub)

**Provenance.** `Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean` of
leanprover-community/mathlib4 PR #43046 (`SchwartzMap.dense_hasCompactSupport`), in the version
contained in PR #43238 at head `78e1b2bbd0d256081c926fccada84fd084653286` (fork `teorth/mathlib4`;
PR base: master `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`, Lean `v4.34.0-rc2`).  Raw source:
`https://raw.githubusercontent.com/leanprover-community/mathlib4/` followed by
`<head>/Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean` (about 190 lines).
Licence: Apache 2.0, see `LICENSE` in this directory (copied from Mathlib).
Upstream's copyright header above is kept.

**Exported interface (used by `Cited/Vendor/PNT/WienerIkehara.lean`, must not change):**
`SchwartzMap.dense_hasCompactSupport : Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}` for
`E` a finite-dimensional real normed space and `F` a real normed space (only `E = ℝ`, `F = ℂ` is
used downstream, through `Dense.inter_open_nonempty`).

**Task (porter).** Replace this stub by the upstream file, verbatim except for these header edits:
delete the `module` line; replace all `public import` / `import` lines by `import Mathlib`; delete
`@[expose] public section` (keep `noncomputable section`).  Keep every declaration name verbatim
(`SchwartzMap.bumpχ`, `χ₀`, `bumpR`, `truncate`, `tendsto_truncate`, `dense_hasCompactSupport`,
…): none of them exists in our Mathlib pin (`065356127b`, Lean `v4.35.0-rc2`), and keeping them
makes the future swap to upstream Mathlib trivial.  Fix drift errors locally (the pin is one week
and one Lean minor version ahead of the PR base: expect a few `simp`/`grind`/`grw`/`field_simp`
changes); record each deviation in a "Porting notes" list in this docstring.  Forbidden: proof
placeholders and every construct flagged by `scripts/audit.sh`.

**Informal proof (upstream).** Fix a smooth bump `χ₀ = 1` on the closed unit ball, supported in
`ball 0 2`, and put `bumpR R x = χ₀ (x / R)`, `truncate f R = bumpR R • f` (a Schwartz map with
compact support).  Every derivative of `bumpR R` of order `i ≥ 1` is `O(R^{-i})` and vanishes on
`‖x‖ < R`, so by Leibniz each Schwartz seminorm `‖x‖^k ‖D^n (truncate f R - f)(x)‖` is `0` for
`‖x‖ < R` and `≤ C ∑_i (n choose i) ‖x‖^{k+1} ‖D^{n-i} f(x)‖ / R` for `‖x‖ ≥ R`; hence
`truncate f R → f` in `𝓢(E, F)` (`tendsto_truncate`) and the compactly supported maps are dense.

**Check.** `bash scripts/check.sh Zeta2Lean/Cited/Vendor/PNT/SchwartzCompactSupport.lean`, then
`bash scripts/build.sh Zeta2Lean.Cited.Vendor.PNT.SchwartzCompactSupport` and
`bash scripts/build.sh Zeta2Lean.Cited.Proofs.WienerIkehara` (everything downstream must still
build: the exported statement is unchanged).
-/

open scoped Topology ContDiff

noncomputable section

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Compactly supported Schwartz functions are dense in `𝓢(E, F)`. -/
theorem dense_hasCompactSupport : Dense {f : 𝓢(E, F) | HasCompactSupport (f : E → F)} := by
  sorry

end SchwartzMap
