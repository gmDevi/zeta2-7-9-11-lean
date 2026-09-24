import Zeta2Lean.Statements

/-!
# Convergence of the Riemann sums of `(x + 1/2)^{-s}` (proof.md P1, P2)

**Theorem.** `Stmt_JConv : ∀ s, HasVolkenborn (halfPow s) (J s)`.  No hypotheses.

**Proof (as formalised).**  Put `w x := (2x+1)⁻¹ ∈ ℚ_[2]` (`jcW`), a 2-adic unit, so that
`halfPow s x = 2^s · w x ^ s` (`jc_halfPow`).  It suffices to show that the Riemann sums
`R_N := volkenbornSum (w ^ s) N` form a Cauchy sequence (`jc_cauchy`): completeness of `ℚ_[2]`
gives a limit `L`, `HasVolkenborn.const_mul` gives `HasVolkenborn (halfPow s) (2^s L)`, and
`HasVolkenborn.volkenborn_eq` identifies `2^s L` with `J s`.

1. `jc_pow_sub_pow`: `‖a‖, ‖b‖ ≤ 1 ⇒ ‖a^m - b^m‖ ≤ ‖a - b‖` (induction, ultrametric).
2. `jc_oddsum` (odd power sums): `‖∑_{x<2^N} w(x)^k‖ ≤ 2^{-N}` for every `k ≥ 0`.  Induction on
   `N`: split `range (2^{N+1})` into two halves and reflect the upper half (`x ↦ 2^{N+1}-1-x`,
   i.e. `u = 2x+1 ↦ 2^{N+2} - u`); then `w(y) ≡ -w(x) (mod 2^{N+2})`, so the sum is
   `(1 + (-1)^k) · ∑_{x<2^N} w(x)^k + O(2^{-N-2})`, and `‖1 + (-1)^k‖ ≤ 1/2`.
3. `jc_shift`: `w(2^N+x) - w(x) = -2^{N+1} w(2^N+x) w(x)`.
4. `jc_mixed`: `‖∑_{x<2^N} w(2^N+x)^i w(x)^l‖ ≤ 2^{-N}` (compare with `∑ w(x)^{i+l}` using 1, 3).
5. `jc_step`: `R_{N+1} - R_N = 2^{-N-1} ∑_{x<2^N} (a_x^s - b_x^s)` with `a_x = w(2^N+x)`,
   `b_x = w(x)`; by `geom_sum₂_mul` and 3 this is `-∑_{j<s} ∑_x a_x^{j+1} b_x^{s-j}` (the factor
   `2^{N+1}` cancels), so `‖R_{N+1} - R_N‖ ≤ 2^{-N}` by 4.  Then `cauchySeq_of_le_geometric`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- `jcW x = (2x+1)⁻¹ ∈ ℚ_[2]`, so that `halfPow s x = 2^s · jcW x ^ s`. -/
private def jcW (x : ℕ) : ℚ_[2] := ((2 * x + 1 : ℕ) : ℚ_[2])⁻¹

private lemma jc_norm_two : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  simpa using (Padic.norm_p (p := 2))

private lemma jc_norm_two_pow (n : ℕ) : ‖(2 : ℚ_[2]) ^ n‖ = (2⁻¹ : ℝ) ^ n := by
  rw [norm_pow, jc_norm_two]

private lemma jc_odd_ne_zero (x : ℕ) : ((2 * x + 1 : ℕ) : ℚ_[2]) ≠ 0 :=
  Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)

private lemma jc_norm_odd (x : ℕ) : ‖((2 * x + 1 : ℕ) : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff, Nat.coprime_two_left]
  exact odd_two_mul_add_one x

private lemma jc_norm_w (x : ℕ) : ‖jcW x‖ = 1 := by
  rw [jcW, norm_inv, jc_norm_odd, inv_one]

/-- `‖a‖, ‖b‖ ≤ 1 ⇒ ‖a^m - b^m‖ ≤ ‖a - b‖` in `ℚ_[2]`. -/
private lemma jc_pow_sub_pow {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖a‖ ^ m * ‖a - b‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) ha) le_rfl (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul]
      calc ‖a ^ m - b ^ m‖ * ‖b‖ ≤ ‖a - b‖ * 1 :=
            mul_le_mul ih hb (norm_nonneg _) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

/-- Odd power sums: `‖∑_{x < 2^N} (2x+1)^{-k}‖ ≤ 2^{-N}` (every `k ≥ 0`). -/
private lemma jc_oddsum (k N : ℕ) : ‖∑ x ∈ range (2 ^ N), jcW x ^ k‖ ≤ (2⁻¹ : ℝ) ^ N := by
  induction N with
  | zero => simp [jcW]
  | succ N ih =>
    have hsplit : ∑ x ∈ range (2 ^ (N + 1)), jcW x ^ k =
        ∑ x ∈ range (2 ^ N), jcW x ^ k + ∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ k := by
      rw [pow_succ, mul_two, Finset.sum_range_add]
    have hrefl : ∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ k =
        ∑ x ∈ range (2 ^ N), jcW (2 ^ N + (2 ^ N - 1 - x)) ^ k :=
      (Finset.sum_range_reflect (fun x => jcW (2 ^ N + x) ^ k) (2 ^ N)).symm
    have key : ∀ x ∈ range (2 ^ N),
        ‖jcW (2 ^ N + (2 ^ N - 1 - x)) ^ k - (-jcW x) ^ k‖ ≤ (2⁻¹ : ℝ) ^ (N + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx
      have h4 : 2 ^ (N + 2) = 4 * 2 ^ N := by rw [pow_add]; ring
      have hnat : 2 * (2 ^ N + (2 ^ N - 1 - x)) + 1 + (2 * x + 1) = 2 ^ (N + 2) := by
        rw [h4]; omega
      have hcast : ((2 * (2 ^ N + (2 ^ N - 1 - x)) + 1 : ℕ) : ℚ_[2]) + ((2 * x + 1 : ℕ) : ℚ_[2])
          = (2 : ℚ_[2]) ^ (N + 2) := by
        rw [← Nat.cast_add, hnat, Nat.cast_pow, Nat.cast_ofNat]
      have hsum : jcW (2 ^ N + (2 ^ N - 1 - x)) - (-jcW x) =
          (2 : ℚ_[2]) ^ (N + 2) * (jcW (2 ^ N + (2 ^ N - 1 - x)) * jcW x) := by
        rw [sub_neg_eq_add, jcW, jcW, inv_add_inv (jc_odd_ne_zero _) (jc_odd_ne_zero _), hcast,
          div_eq_mul_inv, mul_inv]
      calc ‖jcW (2 ^ N + (2 ^ N - 1 - x)) ^ k - (-jcW x) ^ k‖
          ≤ ‖jcW (2 ^ N + (2 ^ N - 1 - x)) - (-jcW x)‖ :=
            jc_pow_sub_pow (jc_norm_w _).le (by rw [norm_neg, jc_norm_w]) k
        _ = (2⁻¹ : ℝ) ^ (N + 2) := by
            rw [hsum, norm_mul, norm_mul, jc_norm_two_pow, jc_norm_w, jc_norm_w, mul_one, mul_one]
        _ ≤ (2⁻¹ : ℝ) ^ (N + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have e2 : ∀ x ∈ range (2 ^ N), jcW x ^ k + jcW (2 ^ N + (2 ^ N - 1 - x)) ^ k =
        (1 + (-1) ^ k) * jcW x ^ k + (jcW (2 ^ N + (2 ^ N - 1 - x)) ^ k - (-jcW x) ^ k) := by
      intro x _
      rw [neg_pow]
      ring
    rw [hsplit, hrefl, ← Finset.sum_add_distrib, Finset.sum_congr rfl e2, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      have h1 : ‖(1 + (-1) ^ k : ℚ_[2])‖ ≤ 2⁻¹ := by
        rcases Nat.even_or_odd k with he | ho
        · rw [he.neg_one_pow, show (1 + 1 : ℚ_[2]) = 2 by norm_num, jc_norm_two]
        · rw [ho.neg_one_pow, add_neg_cancel, norm_zero]
          norm_num
      calc ‖(1 + (-1) ^ k : ℚ_[2])‖ * ‖∑ x ∈ range (2 ^ N), jcW x ^ k‖
          ≤ 2⁻¹ * (2⁻¹ : ℝ) ^ N :=
            mul_le_mul h1 ih (norm_nonneg _) (by norm_num)
        _ = (2⁻¹ : ℝ) ^ (N + 1) := by ring
    · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) key

/-- The difference `jcW (2^N + x) - jcW x = -2^{N+1} jcW (2^N+x) jcW x`. -/
private lemma jc_shift (N x : ℕ) :
    jcW (2 ^ N + x) - jcW x = -(2 : ℚ_[2]) ^ (N + 1) * (jcW (2 ^ N + x) * jcW x) := by
  have hnat : 2 * (2 ^ N + x) + 1 = 2 ^ (N + 1) + (2 * x + 1) := by rw [pow_succ]; ring
  have hcast : ((2 * (2 ^ N + x) + 1 : ℕ) : ℚ_[2]) =
      (2 : ℚ_[2]) ^ (N + 1) + ((2 * x + 1 : ℕ) : ℚ_[2]) := by
    rw [hnat, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  rw [jcW, jcW, inv_sub_inv (jc_odd_ne_zero _) (jc_odd_ne_zero _), hcast, div_eq_mul_inv, mul_inv]
  ring

private lemma jc_norm_shift (N x : ℕ) :
    ‖jcW (2 ^ N + x) - jcW x‖ = (2⁻¹ : ℝ) ^ (N + 1) := by
  rw [jc_shift, norm_mul, norm_mul, norm_neg, jc_norm_two_pow, jc_norm_w, jc_norm_w, mul_one,
    mul_one]

/-- Mixed sums: `‖∑_{x<2^N} jcW (2^N+x)^i jcW x^l‖ ≤ 2^{-N}`. -/
private lemma jc_mixed (i l N : ℕ) :
    ‖∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ i * jcW x ^ l‖ ≤ (2⁻¹ : ℝ) ^ N := by
  have e : ∀ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ i * jcW x ^ l =
      jcW x ^ (i + l) + (jcW (2 ^ N + x) ^ i - jcW x ^ i) * jcW x ^ l := by
    intro x _; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (jc_oddsum _ _) ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro x _
  rw [norm_mul, norm_pow, jc_norm_w, one_pow, mul_one]
  calc ‖jcW (2 ^ N + x) ^ i - jcW x ^ i‖ ≤ ‖jcW (2 ^ N + x) - jcW x‖ :=
        jc_pow_sub_pow (jc_norm_w _).le (jc_norm_w _).le i
    _ = (2⁻¹ : ℝ) ^ (N + 1) := jc_norm_shift N x
    _ ≤ (2⁻¹ : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- One step of the Riemann sums of `jcW ^ s`: `‖R_{N+1} - R_N‖ ≤ 2^{-N}`. -/
private lemma jc_step (s N : ℕ) :
    ‖volkenbornSum (fun x => jcW x ^ s) (N + 1) - volkenbornSum (fun x => jcW x ^ s) N‖ ≤
      (2⁻¹ : ℝ) ^ N := by
  have e1 : ∀ x, jcW (2 ^ N + x) ^ s - jcW x ^ s =
      -(2 : ℚ_[2]) ^ (N + 1) *
        ∑ j ∈ range s, jcW (2 ^ N + x) ^ (j + 1) * jcW x ^ (s - 1 - j + 1) := by
    intro x
    rw [← geom_sum₂_mul, jc_shift, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hsplit : ∑ x ∈ range (2 ^ (N + 1)), jcW x ^ s =
      ∑ x ∈ range (2 ^ N), jcW x ^ s + ∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ s := by
    rw [pow_succ, mul_two, Finset.sum_range_add]
  have hS : ∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ s - ∑ x ∈ range (2 ^ N), jcW x ^ s =
      -(2 : ℚ_[2]) ^ (N + 1) * ∑ j ∈ range s, ∑ x ∈ range (2 ^ N),
        jcW (2 ^ N + x) ^ (j + 1) * jcW x ^ (s - 1 - j + 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => e1 x)
  have hdiff : volkenbornSum (fun x => jcW x ^ s) (N + 1) -
      volkenbornSum (fun x => jcW x ^ s) N =
      -∑ j ∈ range s, ∑ x ∈ range (2 ^ N),
        jcW (2 ^ N + x) ^ (j + 1) * jcW x ^ (s - 1 - j + 1) := by
    simp only [volkenbornSum]
    rw [hsplit]
    set A := ∑ x ∈ range (2 ^ N), jcW x ^ s
    set B := ∑ x ∈ range (2 ^ N), jcW (2 ^ N + x) ^ s
    set T := ∑ j ∈ range s, ∑ x ∈ range (2 ^ N),
        jcW (2 ^ N + x) ^ (j + 1) * jcW x ^ (s - 1 - j + 1)
    have hB : B = A - (2 : ℚ_[2]) ^ (N + 1) * T := by linear_combination hS
    rw [hB]
    field_simp
    ring
  rw [hdiff, norm_neg]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    (fun j _ => jc_mixed _ _ _)

/-- The Riemann sums of `jcW ^ s` are Cauchy. -/
private lemma jc_cauchy (s : ℕ) : CauchySeq (volkenbornSum (fun x => jcW x ^ s)) := by
  refine cauchySeq_of_le_geometric (2⁻¹ : ℝ) 1 (by norm_num) (fun N => ?_)
  rw [dist_eq_norm, norm_sub_rev, one_mul]
  exact jc_step s N

/-- `(x + 1/2)^{-s} = 2^s (2x+1)^{-s}`. -/
private lemma jc_halfPow (s x : ℕ) : halfPow s x = (2 : ℚ_[2]) ^ s * jcW x ^ s := by
  rw [halfPow, jcW, ← mul_pow]
  congr 1
  have e : (x : ℚ_[2]) + 2⁻¹ = ((2 * x + 1 : ℕ) : ℚ_[2]) * 2⁻¹ := by
    push_cast
    ring
  rw [e, mul_inv, inv_inv, mul_comm]

theorem JConv_proof : Stmt_JConv := by
  intro s
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (jc_cauchy s)
  have h1 : HasVolkenborn (fun x => (2 : ℚ_[2]) ^ s * jcW x ^ s) ((2 : ℚ_[2]) ^ s * L) :=
    HasVolkenborn.const_mul _ hL
  have h2 : (fun x => (2 : ℚ_[2]) ^ s * jcW x ^ s) = halfPow s :=
    funext fun x => (jc_halfPow s x).symm
  rw [h2] at h1
  have h3 : J s = (2 : ℚ_[2]) ^ s * L := h1.volkenborn_eq
  rw [h3]
  exact h1

end Zeta2

end
