import Zeta2Lean.Statements

/-!
# L1: the linear form (proof.md §3, Lemma 1; LSZ Lemma 3.3)

**Task.** Prove `Stmt_L1` from `Stmt_JConv`, `Stmt_Translation`, `Stmt_CoeffVanish`:
the Riemann sums of `integrand n` converge to
`ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ + 504 c₇ J₁₀`.

**Informal proof.** In `ℚ_[2]`,
  `integrand n x = ∑_{i=1}^{8} ∑_{k=0}^{n} (i)₃ r_{i,k} · halfPow (i+3) (x + k)`
(cast; `halfPow_eq_cast` in `Defs.lean`).  By `JConv` and `Translation`,
  `HasVolkenborn (fun x => halfPow (i+3) (x+k)) (J (i+3) - (i+3) ∑_{ℓ<k} halfPow (i+4) ℓ)`,
and `∑_{ℓ<k} halfPow (i+4) ℓ = (Ahalf k (i+4) : ℚ_[2])`.  By linearity (`HasVolkenborn.sum`,
`HasVolkenborn.const_mul` in `Defs.lean`) the integral is
  `∑_{i,k} (i)₃ r_{i,k} (J_{i+3} - (i+3) A_k^{(i+4)}) = ∑_{i=1}^{8} (i)₃ c_i J_{i+3} + ρ₀`
(`(i)₃ (i+3) = (i)₄`).  By `Stmt_CoeffVanish`, `c₁ = c₂ = c₄ = c₆ = c₈ = 0`, leaving
`(3)₃ c₃ J₆ + (5)₃ c₅ J₈ + (7)₃ c₇ J₁₀ = 60 c₃ J₆ + 210 c₅ J₈ + 504 c₇ J₁₀`.  Finish by rewriting
the limit value (`HasVolkenborn` is a `Tendsto`, use `Eq ▸` / `convert` after proving the two
values equal by `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_Icc_succ_top` / `decide`-style
expansion of `Icc 1 8`, `push_cast`, `ring`).

**Lean hints.** `HasVolkenborn.sum`, `HasVolkenborn.const_mul`, `HasVolkenborn.add`,
`halfPow_eq_cast`, `volkenbornSum_sum` (all in `Defs.lean`); `Finset.sum_comm`,
`Finset.sum_congr`, `Finset.mul_sum`, `Finset.sum_sub_distrib`, `Rat.cast_sum`, `Rat.cast_mul`,
`Rat.cast_pow`, `Rat.cast_inv`, `Rat.cast_natCast`; for the explicit sum over `Icc 1 8`:
`Finset.sum_Icc_succ_top`, or `show Icc 1 8 = {1,2,…,8} from rfl`/`decide` then `Finset.sum_insert`.

**Numerical check.** `python/mirror.py`, section "Stmt_L1" (`v₂(R_N - S_n) ≫ v₂(S_n)`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem L1_proof (hJ : Stmt_JConv) (hT : Stmt_Translation) (hV : Stmt_CoeffVanish) :
    Stmt_L1 := by
  sorry

end Zeta2

end
