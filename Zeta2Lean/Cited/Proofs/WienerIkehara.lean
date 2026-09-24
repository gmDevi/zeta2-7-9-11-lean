import Zeta2Lean.Cited.Statements
import Zeta2Lean.Cited.Vendor.PNT.WienerIkehara

/-!
# The Wiener–Ikehara theorem, unbundled (PNT track)

**Task.** Prove `Stmt_WienerIkehara`.  No hypotheses.

**Status: complete** as far as this file is concerned — it is the vendored theorem
`WienerIkehara.tendsto_sum_div` (`Cited/Vendor/PNT/WienerIkehara.lean`) applied to the instance
built from the unbundled hypotheses, field by field (`f, C, bound, A, hA, G, hG, hG', hf, hpos`;
the class fields elaborate to exactly the hypotheses of `Stmt_WienerIkehara`, so no conversion is
needed).  The mathematical work is in the two vendored files, which are stubs until ported:
`Cited/Vendor/PNT/SchwartzCompactSupport.lean` (density of compactly supported Schwartz maps) and
`Cited/Vendor/PNT/WienerIkehara.lean` (the Tauberian argument).  Once both are ported,
`#print axioms Zeta2.Cited.WienerIkehara_proof` must show only
`[propext, Classical.choice, Quot.sound]`.

**Future swap.** When Mathlib merges PRs #43046/#43233 and the project deliberately bumps
Mathlib, delete `Cited/Vendor/PNT/` and change the import above to
`Mathlib.NumberTheory.LSeries.WienerIkehara`; this file then compiles unchanged.
-/

namespace Zeta2.Cited

/-- **Wiener–Ikehara** (vendored from mathlib4 PR #43238, `WienerIkehara.tendsto_sum_div`). -/
theorem WienerIkehara_proof : Stmt_WienerIkehara := by
  intro f C A G hbound hA hG hG' hf hpos
  exact @WienerIkehara.tendsto_sum_div
    { f := f, C := C, bound := hbound, A := A, hA := hA, G := G, hG := hG, hG' := hG', hf := hf,
      hpos := hpos }

end Zeta2.Cited
