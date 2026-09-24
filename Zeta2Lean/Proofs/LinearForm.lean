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
`(3)₃ c₃ J₆ + (5)₃ c₅ J₈ + (7)₃ c₇ J₁₀ = 60 c₃ J₆ + 210 c₅ J₈ + 504 c₇ J₁₀`.

**Formal proof (below).**
* `L1_integrand_cast_halfPow`: the cast of `integrand n x` is `∑_{i,k} a_{i,k} · halfPow (i+3) (x+k)`
  with `a_{i,k} = ((i)₃ r_{i,k} : ℚ_[2])`.
* `L1_sum_halfPow_eq_Ahalf`: `∑_{ℓ<k} halfPow s ℓ = (Ahalf k s : ℚ_[2])`.
* `L1_proof`: `HasVolkenborn.sum` twice + `HasVolkenborn.const_mul` of the translated `JConv`
  gives the limit `∑_{i,k} a_{i,k} (J_{i+3} - (i+3) ∑_{ℓ<k} halfPow (i+4) ℓ)`; this is rewritten to
  `∑_{i ∈ [1,8]} (i)₃ c_i J_{i+3} + ρ₀`, the sum over `Icc 1 8` is expanded (`decide` +
  `Finset.sum_insert`), and `c₁ = c₂ = c₄ = c₆ = c₈ = 0` finishes by `push_cast; ring`.
  `J` at odd arguments (`J 4, J 5, …`) only appears multiplied by a vanishing `c_i`.

**Numerical check.** `python/mirror.py`, section "Stmt_L1" (`v₂(R_N - S_n) ≫ v₂(S_n)`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- The integrand, cast to `ℚ_[2]`, in `halfPow` form:
`integrand n x = ∑_{i=1}^{8} ∑_{k=0}^{n} (i)₃ r_{i,k} (x + k + 1/2)^{-(i+3)}`. -/
private theorem L1_integrand_cast_halfPow (n x : ℕ) :
    ((integrand n x : ℚ) : ℚ_[2]) =
      ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
        ((((i : ℚ) * (i + 1) * (i + 2)) * rcoef n i k : ℚ) : ℚ_[2]) * halfPow (i + 3) (x + k) := by
  simp only [integrand, halfPow_eq_cast, Rat.cast_sum, Rat.cast_mul]

/-- `∑_{ℓ<k} halfPow s ℓ = A_k^{(s)}` in `ℚ_[2]`. -/
private theorem L1_sum_halfPow_eq_Ahalf (k s : ℕ) :
    ∑ l ∈ range k, halfPow s l = ((Ahalf k s : ℚ) : ℚ_[2]) := by
  simp only [Ahalf, halfPow_eq_cast, Rat.cast_sum]

theorem L1_proof (hJ : Stmt_JConv) (hT : Stmt_Translation) (hV : Stmt_CoeffVanish) :
    Stmt_L1 := by
  intro n
  -- `a i k = (i)₃ r_{i,k}` in `ℚ_[2]`
  set a : ℕ → ℕ → ℚ_[2] := fun i k =>
    ((((i : ℚ) * (i + 1) * (i + 2)) * rcoef n i k : ℚ) : ℚ_[2]) with ha
  -- linearity + translation: the Riemann sums converge termwise
  have key : HasVolkenborn
      (fun x => ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1), a i k * halfPow (i + 3) (x + k))
      (∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
        a i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 3 + 1) l)) := by
    refine HasVolkenborn.sum _ (fun i _ => ?_)
    refine HasVolkenborn.sum _ (fun k _ => ?_)
    exact (hT (i + 3) k (J (i + 3)) (hJ (i + 3))).const_mul (a i k)
  have e1 : (fun x => ((integrand n x : ℚ) : ℚ_[2])) =
      fun x => ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1), a i k * halfPow (i + 3) (x + k) := by
    funext x
    exact L1_integrand_cast_halfPow n x
  -- the translation terms assemble to `ρ₀` (`(i)₃ (i+3) = (i)₄`)
  have hrho : (rho0 n : ℚ_[2]) = -∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
      a i k * (((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 3 + 1) l) := by
    simp only [rho0, ha, L1_sum_halfPow_eq_Ahalf]
    push_cast
    congr 1
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => ?_))
    ring
  -- the `J`-terms assemble to `(i)₃ c_i J_{i+3}`
  have hc : ∀ i, ∑ k ∈ range (n + 1), a i k =
      (((i : ℚ) * (i + 1) * (i + 2) * csum n i : ℚ) : ℚ_[2]) := by
    intro i
    simp only [ha, csum, Finset.mul_sum, Rat.cast_sum]
  have e2 : ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
        a i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 3 + 1) l) =
      ∑ i ∈ Icc (1 : ℕ) 8, (((i : ℚ) * (i + 1) * (i + 2) * csum n i : ℚ) : ℚ_[2]) * J (i + 3) +
        (rho0 n : ℚ_[2]) := by
    rw [hrho]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc]
    ring
  -- expand `i ∈ [1, 8]`; only `i = 3, 5, 7` survive (`c₁ = 0`, `c_even = 0`)
  have hIcc : (Icc (1 : ℕ) 8) = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have e3 : ∑ i ∈ Icc (1 : ℕ) 8, (((i : ℚ) * (i + 1) * (i + 2) * csum n i : ℚ) : ℚ_[2]) * J (i + 3) =
      60 * (csum n 3 : ℚ_[2]) * J 6 + 210 * (csum n 5 : ℚ_[2]) * J 8 +
        504 * (csum n 7 : ℚ_[2]) * J 10 := by
    rw [hIcc]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have h1 := hV.c1 n
    have h2 := hV.ceven n 2 (by decide)
    have h4 := hV.ceven n 4 (by decide)
    have h6 := hV.ceven n 6 (by decide)
    have h8 := hV.ceven n 8 (by decide)
    simp only [h1, h2, h4, h6, h8]
    push_cast
    ring
  rw [e1]
  rw [e2, e3] at key
  convert key using 1
  ring

end Zeta2

end
