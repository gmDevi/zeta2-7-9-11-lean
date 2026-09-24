import Zeta2Lean.Statements

/-!
# Zeta2Lean.Assembly — the logical skeleton (complete, no gaps)

`main_of_stmts` derives `MainStatement` (convergence of all `J s`, and `ζ₂(7), ζ₂(9), ζ₂(11)` not
all rational) from the top-level lemmas and the prime number theorem, following proof.md §8 (L6):

* `L_m := D_n S_n = a_{m,0} + a_{m,1} ζ₂(7) + a_{m,2} ζ₂(9) + a_{m,3} ζ₂(11)` along `n = 2^m - 1`,
  with integer coefficients `D_n (ρ₀, Z₇, Z₉, Z₁₁)` (`Stmt_L2cor`) and `S_n` the value given by
  `Stmt_L1`;
* `L_m ≠ 0` and `‖L_m‖ ≤ ‖S_n‖ = 2^{-(32n+14-11m)}` (`Stmt_L5`);
* `|a_{m,j}| ≤ D_n · C (n+1)^A 2^{16n}` (`Stmt_L4`), and the product tends to `0`
  (`Stmt_Asymptotic`, which uses PNT);
* Lai's criterion (`Stmt_Criterion`) gives the contradiction.
-/

set_option linter.style.longLine false

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- The `J`-form of `Stmt_L1` equals the `ζ₂`-form `ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9) + Z₁₁ ζ₂(11)`. -/
theorem linear_form_zeta (n : ℕ) :
    (rho0 n : ℚ_[2]) + 60 * (csum n 3 : ℚ_[2]) * J 6 + 210 * (csum n 5 : ℚ_[2]) * J 8 +
        504 * (csum n 7 : ℚ_[2]) * J 10 =
      (rho0 n : ℚ_[2]) + (Z7 n : ℚ_[2]) * zeta2 7 + (Z9 n : ℚ_[2]) * zeta2 9 +
        (Z11 n : ℚ_[2]) * zeta2 11 := by
  simp only [Z7, Z9, Z11, zeta2]
  push_cast
  norm_num
  ring

/-- Transfer of a real bound through `D q = z`. -/
theorem abs_int_le_of_eq {z : ℤ} {D : ℕ} {q : ℚ} (h : (D : ℚ) * q = z) {b : ℝ}
    (hb : |(q : ℝ)| ≤ b) : |(z : ℝ)| ≤ (D : ℝ) * b := by
  have hz : (z : ℝ) = (D : ℝ) * (q : ℝ) := by
    have := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at this
    exact this.symm
  rw [hz, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

/-- Transfer of `D q = z` to `ℚ_[2]`. -/
theorem padic_int_eq {z : ℤ} {D : ℕ} {q : ℚ} (h : (D : ℚ) * q = z) :
    ((z : ℤ) : ℚ_[2]) = (D : ℚ_[2]) * (q : ℚ_[2]) := by
  have := congrArg (fun r : ℚ => (r : ℚ_[2])) h
  push_cast at this
  exact this.symm

/-- **Assembly (proof.md §8, L6).** -/
theorem main_of_stmts (hJ : Stmt_JConv) (hL1 : Stmt_L1) (hL2 : Stmt_L2cor) (hL4 : Stmt_L4)
    (hL5 : Stmt_L5) (hAs : Stmt_Asymptotic) (hCrit : Stmt_Criterion) (hPNT : PNT_Stmt) :
    MainStatement := by
  refine ⟨hJ, ?_⟩
  rintro ⟨⟨q7, hq7⟩, ⟨q9, hq9⟩, ⟨q11, hq11⟩⟩
  obtain ⟨Cst, A, hbd⟩ := hL4
  choose a ha using hL2
  -- the sequences of the criterion, along `n = 2^m - 1`
  let α : Fin 3 → ℚ_[2] := ![zeta2 7, zeta2 9, zeta2 11]
  let a₀ : ℕ → ℤ := fun m => a (2 ^ m - 1) 0
  let a' : ℕ → Fin 3 → ℤ := fun m j => a (2 ^ m - 1) j.succ
  let B : ℕ → ℝ := fun m => (Dn (2 ^ m - 1) : ℝ) * archBound Cst A (2 ^ m - 1)
  -- the value of the linear form
  let I : ℕ → ℚ_[2] := fun n =>
    (rho0 n : ℚ_[2]) + (Z7 n : ℚ_[2]) * zeta2 7 + (Z9 n : ℚ_[2]) * zeta2 9 +
      (Z11 n : ℚ_[2]) * zeta2 11
  have hLform : ∀ m, (a₀ m : ℚ_[2]) + ∑ j, (a' m j : ℚ_[2]) * α j =
      (Dn (2 ^ m - 1) : ℚ_[2]) * I (2 ^ m - 1) := by
    intro m
    obtain ⟨h0, h1, h2, h3⟩ := ha (2 ^ m - 1)
    simp only [a₀, a', α, I, Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [padic_int_eq h0, padic_int_eq h1, padic_int_eq h2]
    have h3' : ((a (2 ^ m - 1) (Fin.succ 2) : ℤ) : ℚ_[2]) =
        (Dn (2 ^ m - 1) : ℚ_[2]) * (Z11 (2 ^ m - 1) : ℚ_[2]) := padic_int_eq h3
    rw [h3']
    ring
  have hInorm : ∀ m, 2 ≤ m → ‖I (2 ^ m - 1)‖ = (2 : ℝ) ^ (-target m) := by
    intro m hm
    apply hL5 m hm
    have := hL1 (2 ^ m - 1)
    rwa [linear_form_zeta] at this
  have hB0 : ∀ m, 0 ≤ archBound Cst A (2 ^ m - 1) :=
    fun m => (abs_nonneg _).trans (hbd (2 ^ m - 1)).1
  have hDn_norm : ∀ n, ‖(Dn n : ℚ_[2])‖ ≤ 1 := by
    intro n
    have := Padic.norm_int_le_one (p := 2) (Dn n : ℤ)
    simpa using this
  apply hCrit 3 α a₀ a' B
  · -- `|a_{m,0}| ≤ B m`
    intro m
    exact abs_int_le_of_eq (ha (2 ^ m - 1)).1 (hbd (2 ^ m - 1)).1
  · -- `|a_{m,j}| ≤ B m`
    intro m j
    obtain ⟨_, h1, h2, h3⟩ := ha (2 ^ m - 1)
    obtain ⟨_, b1, b2, b3⟩ := hbd (2 ^ m - 1)
    fin_cases j
    · exact abs_int_le_of_eq h1 b1
    · exact abs_int_le_of_eq h2 b2
    · exact abs_int_le_of_eq h3 b3
  · -- the linear forms are eventually non-zero
    apply Filter.Eventually.frequently
    filter_upwards [Filter.eventually_ge_atTop 2] with m hm
    rw [hLform m]
    apply mul_ne_zero
    · exact_mod_cast (Dn_pos (2 ^ m - 1)).ne'
    · intro h0
      have := hInorm m hm
      rw [h0, norm_zero] at this
      exact absurd this.symm (by positivity)
  · -- `B m · ‖L_m‖ → 0`
    have hlim := hAs hPNT Cst A
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · filter_upwards with m
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 m)) (norm_nonneg _)
    · filter_upwards [Filter.eventually_ge_atTop 2] with m hm
      rw [hLform m, norm_mul, hInorm m hm]
      have hD : ‖(Dn (2 ^ m - 1) : ℚ_[2])‖ ≤ 1 := hDn_norm _
      have hBm : 0 ≤ B m := mul_nonneg (Nat.cast_nonneg _) (hB0 m)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-target m) := by positivity
      calc B m * (‖(Dn (2 ^ m - 1) : ℚ_[2])‖ * (2 : ℝ) ^ (-target m))
          ≤ B m * (1 * (2 : ℝ) ^ (-target m)) := by gcongr
        _ = (Dn (2 ^ m - 1) : ℝ) * archBound Cst A (2 ^ m - 1) * (2 : ℝ) ^ (-target m) := by
          simp only [B]; ring
  · -- all three values rational
    intro j
    fin_cases j
    · exact ⟨q7, hq7⟩
    · exact ⟨q9, hq9⟩
    · exact ⟨q11, hq11⟩

end Zeta2

end
