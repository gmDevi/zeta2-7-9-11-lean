import Zeta2Lean.Statements

/-!
# Translation formula for `(t + 1/2)^{-s}` (proof.md P1; LSZ Lemma 2.4; Robert §5.3)

**Task.** Prove `Stmt_Translation`:
`HasVolkenborn (halfPow s) I → HasVolkenborn (fun x => halfPow s (x + k)) (I - s ∑_{ℓ<k} halfPow (s+1) ℓ)`.
No hypotheses (the convergence of the unshifted sums is an assumption of the statement).

**Informal proof.** Let `f = halfPow s`.  For every `N`,
  `∑_{x<2^N} f(x+k) = ∑_{x<2^N} f(x) + ∑_{ℓ<k} (f(ℓ + 2^N) - f(ℓ))`
(induction on `k`, or `Finset.sum_range_add_sum_Ico` twice), hence
  `volkenbornSum (f(·+k)) N = volkenbornSum f N + ∑_{ℓ<k} (f(ℓ + 2^N) - f(ℓ)) / 2^N`.
For fixed `ℓ`, with `u = ℓ + 1/2` (`‖u‖ = 2`, `u⁻¹ = 2/(2ℓ+1)`) and `h = 2^N` (`‖h‖ = 2^{-N} → 0`):
  `((u+h)^{-s} - u^{-s}) / h + s u^{-s-1} = h · E(ℓ, N)`  with `‖E(ℓ,N)‖ ≤ C_{s}`
(algebra: `(u+h)^{-s} - u^{-s} + s h u^{-s-1} = h² Q(u,h) / (u^{s+1}(u+h)^s)`, `Q ∈ ℤ[u,h]`; in
terms of `u' = 2ℓ+1`, `h' = 2^{N+1}` everything is a 2-adic unit or integer).  So each summand
tends to `-s · halfPow (s+1) ℓ`; add the finitely many limits (`tendsto_finsetSum`) to the
hypothesis `volkenbornSum f N → I` (`Filter.Tendsto.add`).

**Lean hints.** `Finset.sum_range_add_sum_Ico`, `Finset.sum_range_succ`, `Finset.sum_sub_distrib`,
`Filter.Tendsto.add`, `Filter.Tendsto.sub`, `tendsto_finsetSum`, `tendsto_pow_atTop_nhds_zero_of_lt_one`
(for `2^{-N} → 0` in `ℝ`), `Padic.norm_p_pow`, `Padic.nonarchimedean`, `Padic.norm_int_le_one`,
`squeeze_zero_norm` / `tendsto_iff_norm_sub_tendsto_zero` (for `‖a_N - L‖ ≤ C 2^{-N} → 0`),
`volkenbornSum_add` and `HasVolkenborn.add`, `HasVolkenborn.sum` (in `Defs.lean`).
Writing `halfPow s x = 2^s * ((2*x+1 : ℕ) : ℚ_[2])⁻¹ ^ s` first is convenient.

**Numerical check.** `python/mirror.py`, section "J_s ...": `v₂(R_12 - (J_s - s A_k)) ≥ 20`.

**Formal proof (as done below).**  No explicit error bound is needed; the difference quotient is
handled by exact algebra plus continuity.  With `a = u⁻¹`, `b_N = (u + 2^N)⁻¹` we have
`b_N - a = -2^N a b_N`, so by `geom_sum₂_mul`
  `2^{-N} (b_N^s - a^s) = -(∑_{j<s} b_N^j a^{s-1-j}) · a · b_N`   (`translation_diff_quot`).
Since `‖2‖ < 1`, `2^N → 0` in `ℚ_[2]`, hence `b_N → a` (`Filter.Tendsto.inv₀`, `u ≠ 0`), and the
right-hand side is a continuous (polynomial) function of `b_N`, so it tends to
`-(∑_{j<s} a^j a^{s-1-j}) a a = -s a^{s+1}` (`geom_sum₂_self`).  The shift identity is
`translation_sum_shift` (induction on `k`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- Shifting the summation range: `∑_{x<M} f(x+k) = ∑_{x<M} f(x) + ∑_{ℓ<k} (f(ℓ+M) - f(ℓ))`. -/
private theorem translation_sum_shift (f : ℕ → ℚ_[2]) (M k : ℕ) :
    ∑ x ∈ range M, f (x + k) = ∑ x ∈ range M, f x + ∑ l ∈ range k, (f (l + M) - f l) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Finset.sum_range_succ' (fun x => f (x + k)) M
    have h2 := Finset.sum_range_succ (fun x => f (x + k)) M
    simp only [zero_add] at h1 h2
    have h3 : ∑ x ∈ range M, f (x + (k + 1)) = ∑ x ∈ range M, f (x + 1 + k) :=
      Finset.sum_congr rfl fun x _ => by rw [show x + (k + 1) = x + 1 + k by ring]
    rw [h3, Finset.sum_range_succ, add_comm k M]
    linear_combination (h1.symm.trans h2) + ih

/-- `‖2‖ < 1` in `ℚ_[2]`. -/
private theorem translation_two_norm_lt_one : ‖(2 : ℚ_[2])‖ < 1 := by
  have h := Padic.norm_p_lt_one (p := 2)
  simpa using h

/-- `x + 1/2 ≠ 0` in `ℚ_[2]` for `x ∈ ℕ` (so `halfPow` never divides by zero). -/
private theorem translation_half_ne_zero (x : ℕ) : (x : ℚ_[2]) + 2⁻¹ ≠ 0 := by
  have h : ((((x : ℚ) + 2⁻¹ : ℚ)) : ℚ_[2]) = (x : ℚ_[2]) + 2⁻¹ := by push_cast; ring
  rw [← h]
  have : (x : ℚ) + 2⁻¹ ≠ 0 := by positivity
  exact Rat.cast_ne_zero.mpr this

/-- Exact difference quotient of `u ↦ u^{-s}`:
`h⁻¹ ((u+h)^{-s} - u^{-s}) = -(∑_{j<s} (u+h)^{-j} u^{-(s-1-j)}) u⁻¹ (u+h)⁻¹`. -/
private theorem translation_diff_quot {K : Type*} [Field K] (u h : K) (hu : u ≠ 0)
    (huh : u + h ≠ 0) (hh : h ≠ 0) (s : ℕ) :
    h⁻¹ * ((u + h)⁻¹ ^ s - u⁻¹ ^ s) =
      -(∑ j ∈ range s, (u + h)⁻¹ ^ j * u⁻¹ ^ (s - 1 - j)) * u⁻¹ * (u + h)⁻¹ := by
  have hba : (u + h)⁻¹ - u⁻¹ = -h * u⁻¹ * (u + h)⁻¹ := by
    field_simp
    ring
  have hG := geom_sum₂_mul (u + h)⁻¹ u⁻¹ s
  have hhh : h⁻¹ * h = 1 := inv_mul_cancel₀ hh
  rw [← hG, hba]
  linear_combination
    (-(∑ j ∈ range s, (u + h)⁻¹ ^ j * u⁻¹ ^ (s - 1 - j)) * u⁻¹ * (u + h)⁻¹) * hhh

/-- For fixed `ℓ`, `2^{-N} (f(ℓ + 2^N) - f(ℓ)) → f'(ℓ) = -s (ℓ+1/2)^{-s-1}` for `f = halfPow s`. -/
private theorem translation_key (s l : ℕ) :
    Tendsto (fun N : ℕ => ((2 : ℚ_[2]) ^ N)⁻¹ * (halfPow s (l + 2 ^ N) - halfPow s l)) atTop
      (𝓝 (-(s : ℚ_[2]) * halfPow (s + 1) l)) := by
  have hu : (l : ℚ_[2]) + 2⁻¹ ≠ 0 := translation_half_ne_zero l
  have hpow : Tendsto (fun N : ℕ => (2 : ℚ_[2]) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one translation_two_norm_lt_one
  have hb : Tendsto (fun N : ℕ => ((l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N)⁻¹) atTop
      (𝓝 ((l : ℚ_[2]) + 2⁻¹)⁻¹) := by
    have h1 : Tendsto (fun N : ℕ => (l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N) atTop
        (𝓝 ((l : ℚ_[2]) + 2⁻¹ + 0)) :=
      tendsto_const_nhds.add hpow
    rw [add_zero] at h1
    exact h1.inv₀ hu
  have hFc : Continuous (fun b : ℚ_[2] =>
      -(∑ j ∈ range s, b ^ j * ((l : ℚ_[2]) + 2⁻¹)⁻¹ ^ (s - 1 - j)) * ((l : ℚ_[2]) + 2⁻¹)⁻¹ * b) := by
    fun_prop
  have hlim := (hFc.tendsto _).comp hb
  have hFu : -(∑ j ∈ range s, ((l : ℚ_[2]) + 2⁻¹)⁻¹ ^ j * ((l : ℚ_[2]) + 2⁻¹)⁻¹ ^ (s - 1 - j)) *
      ((l : ℚ_[2]) + 2⁻¹)⁻¹ * ((l : ℚ_[2]) + 2⁻¹)⁻¹ = -(s : ℚ_[2]) * halfPow (s + 1) l := by
    rw [geom_sum₂_self]
    unfold halfPow
    cases s with
    | zero => simp
    | succ t =>
      simp only [add_tsub_cancel_right]
      push_cast
      ring
  have heq : ∀ N : ℕ, ((2 : ℚ_[2]) ^ N)⁻¹ * (halfPow s (l + 2 ^ N) - halfPow s l) =
      -(∑ j ∈ range s, ((l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N)⁻¹ ^ j *
        ((l : ℚ_[2]) + 2⁻¹)⁻¹ ^ (s - 1 - j)) * ((l : ℚ_[2]) + 2⁻¹)⁻¹ *
        ((l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N)⁻¹ := by
    intro N
    have h2 : ((l + 2 ^ N : ℕ) : ℚ_[2]) + 2⁻¹ = (l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N := by
      push_cast; ring
    have hne : (l : ℚ_[2]) + 2⁻¹ + (2 : ℚ_[2]) ^ N ≠ 0 := by
      rw [← h2]; exact translation_half_ne_zero _
    unfold halfPow
    rw [h2]
    exact translation_diff_quot _ _ hu hne (pow_ne_zero _ two_ne_zero) s
  rw [← hFu]
  exact hlim.congr (fun N => (heq N).symm)

theorem Translation_proof : Stmt_Translation := by
  intro s k I hI
  unfold HasVolkenborn at *
  have h1 : volkenbornSum (fun x => halfPow s (x + k)) = fun N =>
      volkenbornSum (halfPow s) N +
        ∑ l ∈ range k, ((2 : ℚ_[2]) ^ N)⁻¹ * (halfPow s (l + 2 ^ N) - halfPow s l) := by
    funext N
    unfold volkenbornSum
    rw [translation_sum_shift (halfPow s) (2 ^ N) k, mul_add, Finset.mul_sum (range k)]
  have h2 : I - (s : ℚ_[2]) * ∑ l ∈ range k, halfPow (s + 1) l =
      I + ∑ l ∈ range k, (-(s : ℚ_[2]) * halfPow (s + 1) l) := by
    rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [h1, h2]
  exact hI.add (tendsto_finsetSum _ fun l _ => translation_key s l)

end Zeta2

end
