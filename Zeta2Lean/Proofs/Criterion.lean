import Zeta2Lean.Statements

/-!
# Lai's irrationality criterion (proof.md P4; Lai arXiv:2304.00816, Lemma 2.1)

**Task.** Prove `Stmt_Criterion`: if `|a_{m,j}| ≤ B_m` (all `j`, including `j = 0`), the forms
`L_m = a_{m,0} + ∑_j a_{m,j} α_j ∈ ℚ_[2]` are frequently non-zero, and `B_m ‖L_m‖ → 0`, then not all
`α_j` are rational.  No hypotheses.

**Informal proof.** Suppose `α_j = q_j ∈ ℚ` for all `j`.  Let `D ≥ 1` be a common denominator
(e.g. `D = ∏_j (q_j).den`), so `D q_j ∈ ℤ`.  Then `D L_m = D a_{m,0} + ∑_j a_{m,j} (D q_j)` is an
integer `z_m`, with `|z_m| ≤ B_m · E`, `E := D + ∑_j |D q_j|`.  For the (frequent) `m` with
`L_m ≠ 0`: `z_m ≠ 0`, and for a non-zero integer `‖(z : ℚ_[2])‖ ≥ 1/|z|` (since `2^{v₂(z)} ∣ z`,
`2^{v₂(z)} ≤ |z|`).  Hence `B_m ‖L_m‖ = B_m ‖z_m‖ / ‖D‖ ≥ B_m / (|z_m| ‖D‖) ≥ 1/(E ‖D‖) > 0`
(note `B_m > 0` there, because `1 ≤ |z_m| ≤ B_m E`).  This contradicts `B_m ‖L_m‖ → 0`
(take `ε = 1/(E‖D‖)`: eventually `< ε`, but frequently `≥ ε`).

**Formal proof (as done below).** Slightly streamlined: since `‖D‖ ≤ 1`, `‖z_m‖ = ‖D‖ ‖L_m‖ ≤ ‖L_m‖`,
so `1 ≤ ‖z_m‖ |z_m| ≤ ‖L_m‖ · B_m E` whenever `L_m ≠ 0`, i.e. `B_m ‖L_m‖ ≥ 1/E`.
* `criterion_one_le_norm_mul_abs`: `z ≠ 0 → 1 ≤ ‖(z : ℚ_[2])‖ * |z|`.
* `criterion_common_denom`: `D = ∏_j den(q_j) > 0` and integers `p_j` with `p_j = D q_j`.
* `criterion_lower_bound`: the uniform bound `1 ≤ E (b ‖L‖)` for all integer coefficient vectors
  bounded by `b` with `L ≠ 0`.
* `Criterion_proof`: eventually `B_m ‖L_m‖ < 1/E` and frequently `L_m ≠ 0`: contradiction.
The case `k = 0` needs no special treatment (then `D = 1`, `E = 1`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- For a non-zero integer `z`, `1 ≤ ‖(z : ℚ_[2])‖ * |z|` (since `2^{v₂(z)} ∣ z`, so
`2^{v₂(z)} ≤ |z|`, while `‖z‖ = 2^{-v₂(z)}`). -/
private lemma criterion_one_le_norm_mul_abs (z : ℤ) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℚ_[2])‖ * |(z : ℝ)| := by
  have hz' : (z : ℚ_[2]) ≠ 0 := by exact_mod_cast hz
  rw [Padic.norm_eq_zpow_neg_valuation hz', Padic.valuation_intCast]
  have hdvd : (2 : ℤ) ^ padicValInt 2 z ∣ |z| :=
    (dvd_abs _ _).mpr (by exact_mod_cast padicValInt_dvd (p := 2) z)
  have hle : (2 : ℤ) ^ padicValInt 2 z ≤ |z| := Int.le_of_dvd (abs_pos.mpr hz) hdvd
  have hle' : (2 : ℝ) ^ padicValInt 2 z ≤ |(z : ℝ)| := by
    have := (Int.cast_le (R := ℝ)).mpr hle
    push_cast at this
    exact this
  have h2 : (0 : ℝ) < 2 ^ padicValInt 2 z := by positivity
  rw [zpow_neg, zpow_natCast]
  push_cast
  rw [inv_mul_eq_div, le_div_iff₀ h2, one_mul]
  exact hle'

/-- A common denominator: `D = ∏_j den(q_j) > 0` and integers `p_j` with `p_j = D q_j`. -/
private lemma criterion_common_denom (k : ℕ) (q : Fin k → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ p : Fin k → ℤ, ∀ j, ((p j : ℤ) : ℚ) = (D : ℚ) * q j := by
  refine ⟨∏ j, (q j).den, Finset.prod_pos (fun j _ => (q j).den_pos), ?_⟩
  refine ⟨fun j => (q j).num * (((∏ i, (q i).den) / (q j).den : ℕ) : ℤ), ?_⟩
  intro j
  have hdvd : (q j).den ∣ ∏ i, (q i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨c, hc⟩ := hdvd
  beta_reduce
  rw [hc, Nat.mul_div_cancel_left c (q j).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num (q j)]
  ring

/-- The uniform lower bound behind Lai's criterion: if all `α_j = q_j` are rational, there is
`E > 0` such that every non-zero form `L = a₀ + ∑_j a_j α_j` with integer coefficients bounded by
`b` satisfies `1 ≤ E · (b ‖L‖)`. -/
private lemma criterion_lower_bound (k : ℕ) (α : Fin k → ℚ_[2]) (q : Fin k → ℚ)
    (hq : ∀ j, α j = q j) :
    ∃ E : ℝ, 0 < E ∧ ∀ (a₀ : ℤ) (a : Fin k → ℤ) (b : ℝ), |(a₀ : ℝ)| ≤ b →
      (∀ j, |(a j : ℝ)| ≤ b) → (a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j ≠ 0 →
      1 ≤ E * (b * ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖) := by
  obtain ⟨D, hDpos, p, hp⟩ := criterion_common_denom k q
  have hE : (0 : ℝ) < D + ∑ j, |(p j : ℝ)| :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast hDpos)
      (Finset.sum_nonneg (fun j _ => abs_nonneg _))
  refine ⟨D + ∑ j, |(p j : ℝ)|, hE, ?_⟩
  intro a₀ a b h0 ha hL
  have hb : 0 ≤ b := le_trans (abs_nonneg _) h0
  -- the integer `z = D · L`
  have hzL : (((D : ℤ) * a₀ + ∑ j, a j * p j : ℤ) : ℚ_[2]) =
      (D : ℚ_[2]) * ((a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j) := by
    push_cast
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have h' : ((p j : ℤ) : ℚ_[2]) = (D : ℚ_[2]) * α j := by
      rw [hq j, ← Rat.cast_intCast, hp j]
      push_cast
      ring
    rw [h']
    ring
  set z : ℤ := (D : ℤ) * a₀ + ∑ j, a j * p j with hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, eq_comm, mul_eq_zero] at hzL
    rcases hzL with h1 | h1
    · exact absurd h1 (by exact_mod_cast hDpos.ne')
    · exact hL h1
  have hzb : |(z : ℝ)| ≤ b * (D + ∑ j, |(p j : ℝ)|) := by
    rw [hz]
    push_cast
    calc |(D : ℝ) * a₀ + ∑ j, (a j : ℝ) * p j|
        ≤ |(D : ℝ) * a₀| + |∑ j, (a j : ℝ) * p j| := abs_add_le _ _
      _ ≤ D * b + ∑ j, b * |(p j : ℝ)| := by
          gcongr
          · rw [abs_mul, Nat.abs_cast]
            gcongr
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            gcongr with j
            rw [abs_mul]
            gcongr
            exact ha j
      _ = b * (D + ∑ j, |(p j : ℝ)|) := by rw [mul_add, Finset.mul_sum]; ring
  have hnorm : ‖(z : ℚ_[2])‖ ≤ ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖ := by
    rw [hzL, norm_mul]
    have hD1 : ‖(D : ℚ_[2])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := 2) (D : ℤ)
      simpa using this
    calc ‖(D : ℚ_[2])‖ * ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖
        ≤ 1 * ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖ := by gcongr
      _ = _ := one_mul _
  have key := criterion_one_le_norm_mul_abs z hz0
  calc (1 : ℝ) ≤ ‖(z : ℚ_[2])‖ * |(z : ℝ)| := key
    _ ≤ ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖ * (b * (D + ∑ j, |(p j : ℝ)|)) := by
        gcongr
    _ = (D + ∑ j, |(p j : ℝ)|) * (b * ‖(a₀ : ℚ_[2]) + ∑ j, (a j : ℚ_[2]) * α j‖) := by ring

/-- **Lai's irrationality criterion** (proof.md P4; Lai Lemma 2.1). -/
theorem Criterion_proof : Stmt_Criterion := by
  intro k α a₀ a B h0 ha hfreq htend hrat
  choose q hq using hrat
  obtain ⟨E, hE, hbound⟩ := criterion_lower_bound k α q hq
  have hev : ∀ᶠ m in atTop,
      B m * ‖(a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j‖ < 1 / E :=
    htend.eventually_lt_const (one_div_pos.mpr hE)
  obtain ⟨m, hm0, hm1⟩ := (hfreq.and_eventually hev).exists
  have h1 := hbound (a₀ m) (a m) (B m) (h0 m) (ha m) hm0
  have h2 : E * (B m * ‖(a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j‖) < E * (1 / E) :=
    mul_lt_mul_of_pos_left hm1 hE
  rw [mul_one_div_cancel hE.ne'] at h2
  linarith

end Zeta2

end
