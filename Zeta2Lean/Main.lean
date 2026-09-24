import Zeta2Lean.Assembly
import Zeta2Lean.Proofs.JConvergence
import Zeta2Lean.Proofs.Translation
import Zeta2Lean.Proofs.Criterion
import Zeta2Lean.Proofs.PartialFractions
import Zeta2Lean.Proofs.CoeffVanish
import Zeta2Lean.Proofs.LinearForm
import Zeta2Lean.Proofs.BuildingBlock
import Zeta2Lean.Proofs.DenomL2a
import Zeta2Lean.Proofs.DenomL2b
import Zeta2Lean.Proofs.ResidueForm
import Zeta2Lean.Proofs.AndrewsApplied
import Zeta2Lean.Proofs.ClosedFormFJ
import Zeta2Lean.Proofs.KummerFJ
import Zeta2Lean.Proofs.DenomL2c
import Zeta2Lean.Proofs.DenomCor
import Zeta2Lean.Proofs.ArchBound
import Zeta2Lean.Proofs.Asymptotics
import Zeta2Lean.Proofs.DeltaCalculus
import Zeta2Lean.Proofs.DeltaFunctions
import Zeta2Lean.Proofs.Digits
import Zeta2Lean.Proofs.Leibniz
import Zeta2Lean.Proofs.LeibnizTermBound
import Zeta2Lean.Proofs.DominantTerm
import Zeta2Lean.Proofs.Nonvanishing

set_option linter.style.header false

/-!
# Zeta2Lean.Main — the main theorem

Wires the proofs of all non-cited statements into `main_of_stmts`.  The only remaining
hypotheses are the two cited results (`PNT_Stmt`, `Andrews_Stmt`, see `Statements.lean`).

Dependency graph (see `BLUEPRINT.md`):
* `L1 ← JConv, Translation, CoeffVanish ← PF`
* `L2cor ← L2a, L2b, L2c`;  `L2a ← BlockF`;  `L2b ← PF, L2a`;
  `L2c ← ResidueForm, AndrewsApplied (← Andrews), FJClosed, FJKummer`
* `L4`, `Asymptotic` (uses PNT), `Criterion`
* `L5 ← Delta, Leibniz (← PF), LeibTermBound, L5Dom`;
  `LeibTermBound, L5Dom ← Delta, DeltaFun (← Delta), Digit`
-/

namespace Zeta2

/-- **Main theorem.**  Assuming the prime number theorem and Andrews' transformation (both
published, cited results), the Riemann sums defining the 2-adic values `J s` converge for all `s`,
and the 2-adic zeta values `ζ₂(7)`, `ζ₂(9)`, `ζ₂(11)` are not all rational. -/
theorem zeta2_7_9_11_not_all_rational (hPNT : PNT_Stmt) (hAndrews : Andrews_Stmt) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q)) :=
  main_of_stmts JConv_proof
    (L1_proof JConv_proof Translation_proof (CoeffVanish_proof PF_proof))
    (L2cor_proof (L2a_proof BlockF_proof) (L2b_proof PF_proof (L2a_proof BlockF_proof))
      (L2c_proof ResidueForm_proof (AndrewsApplied_proof hAndrews) FJClosed_proof
        FJKummer_proof))
    L4_proof
    (L5_proof Delta_proof (Leibniz_proof PF_proof)
      (LeibTermBound_proof Delta_proof (DeltaFun_proof Delta_proof) Digit_proof)
      (L5Dom_proof Delta_proof (DeltaFun_proof Delta_proof) Digit_proof))
    Asymptotic_proof Criterion_proof hPNT

end Zeta2

#print axioms Zeta2.zeta2_7_9_11_not_all_rational
