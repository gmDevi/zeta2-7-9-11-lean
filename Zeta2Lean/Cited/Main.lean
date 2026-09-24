import Zeta2Lean.Main
import Zeta2Lean.Cited.Assembly
import Zeta2Lean.Cited.Proofs.WienerIkehara
import Zeta2Lean.Cited.Proofs.PfaffSaalschutz
import Zeta2Lean.Cited.Proofs.UnitPair
import Zeta2Lean.Cited.Proofs.BaileyLemma
import Zeta2Lean.Cited.Proofs.ChainSum
import Zeta2Lean.Cited.Proofs.ChainStep

/-!
# Zeta2Lean.Cited.Main — the main theorem without cited hypotheses

Wires the proofs of the sub-lemma statements of `Cited/Statements.lean` into
`Cited/Assembly.lean`, giving `PNT_proof : PNT_Stmt` and `Andrews_proof : Andrews_Stmt`, and
applies the frozen, kernel-checked `zeta2_7_9_11_not_all_rational` (`Zeta2Lean/Main.lean`) to them.

Dependency graph (see `Cited/Statements.lean`):
* `PNT_Stmt ⇐ WienerIkehara`; the latter is the vendored theorem
  (`Vendor/PNT/WienerIkehara ⇐ Vendor/PNT/SchwartzCompactSupport`, by import)
* `Andrews_Stmt ⇐ BPChain ⇐ UnitPair, BaileyLemma (⇐ PPS), ChainStep (⇐ SumChainsSucc)`

This module is not imported by the root `Zeta2Lean.lean` yet (the verified default build stays
as it is); build it explicitly with `bash scripts/build.sh Zeta2Lean.Cited.Main`.  While proof
stubs remain, the `#print axioms` lines below also list `sorryAx`; once every file under
`Cited/` is complete they must list exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Zeta2

/-- **The prime number theorem** `ψ(x)/x → 1`, proved (Wiener–Ikehara, vendored from
mathlib4 PRs #43046/#43233/#43238). -/
theorem PNT_proof : PNT_Stmt :=
  Cited.pnt_of_stmts Cited.WienerIkehara_proof

/-- **Andrews' transformation** (Krattenthaler–Rivoal, Théorème 8), proved via the `q = 1`
Bailey chain and the polynomial Pfaff–Saalschütz identity. -/
theorem Andrews_proof : Andrews_Stmt :=
  Cited.andrews_of_stmts Cited.UnitPair_proof (Cited.BaileyLemma_proof Cited.PPS_proof)
    (Cited.ChainStep_proof Cited.SumChainsSucc_proof)

/-- **Main theorem, unconditional.**  The Riemann sums defining every `J s` converge, and the
2-adic zeta values `ζ₂(7)`, `ζ₂(9)`, `ζ₂(11)` are not all rational. -/
theorem zeta2_7_9_11_not_all_rational_unconditional : MainStatement :=
  zeta2_7_9_11_not_all_rational PNT_proof Andrews_proof

end Zeta2

#print axioms Zeta2.PNT_proof
#print axioms Zeta2.Andrews_proof
#print axioms Zeta2.zeta2_7_9_11_not_all_rational_unconditional
