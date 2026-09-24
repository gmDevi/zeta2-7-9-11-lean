import Zeta2Lean.Statements

/-!
# The exponent computation (proof.md §4.4 last line, §8; uses PNT)

**Task.** Prove `Stmt_Asymptotic`: assuming `PNT_Stmt` (`ψ(x)/x → 1`), for all `Cst : ℝ`, `A : ℕ`,
  `D_n · Cst (n+1)^A 2^{16n} · 2^{-target m} → 0`  along `n = 2^m - 1`, `m → ∞`,
where `target m = 32n + 14 - 11m`.  (Uses only the *upper* half of PNT, `ψ(x) ≤ (1+δ)x`.)

**Informal proof.** Let `n = 2^m - 1` (`n → ∞`).  `D_n ≤ d_n^{12}/Φ_n` (`Nat.cast_div_le`), so
  `log D_n ≤ 12 log d_n - log Φ_n`,  `log d_n = ψ(n)` (`Chebyshev.psi_eq_log_lcmUpto`),
  `log Φ_n = ∑_{p ≤ n, p ≥ 11, p² > 2n} log p ≥ θ(n) - θ(10) - θ(√(2n)) ≥ θ(n) - log 4 · (10 + √(2n))`
(the complement of the index set inside the primes `≤ n` consists of primes `≤ 10` or `≤ √(2n)`;
`Chebyshev.theta_le_log4_mul_x`), and `θ(n) ≥ ψ(n) - 2√n log n` (`Chebyshev.psi_sub_theta_le`).
Hence `log D_n ≤ 11 ψ(n) + 2√n log n + log 4 · (10 + √(2n))`.  By PNT, for `δ = 1/400` and `n`
large, `ψ(n) ≤ (1+δ) n`, so `log D_n ≤ 11.03 n + o(n)`.  The logarithm of the quantity is (for
`Cst > 0`; the cases `Cst ≤ 0` are trivial or follow by `|·|`)
  `log D_n + log Cst + A m log 2 + 16 n log 2 - (32 n + 14 - 11 m) log 2
     ≤ (11.03 - 16 log 2) n + o(n) → -∞`,
since `16 log 2 > 16 · 0.6931471803 > 11.09` (`Real.log_two_gt_d9`).  So the quantity tends to `0`.

**Lean hints.** `Chebyshev.psi`, `Chebyshev.theta`, `Chebyshev.psi_eq_log_lcmUpto`,
`Chebyshev.theta_eq_sum_primesLE`, `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_sub_theta_le`,
`Chebyshev.theta_le_psi`, `Chebyshev.theta_mono`, `Nat.primesLE`, `Nat.cast_div_le`, `Real.log_prod`,
`Real.log_le_log_iff`, `Real.log_pow`, `Real.exp_log`, `Real.tendsto_exp_atBot`,
`Real.log_two_gt_d9`,
`isLittleO_pow_exp_pos_mul_atTop`, `Real.isLittleO_log_id_atTop`,
`tendsto_pow_atTop_atTop_of_one_lt` (for `2^m → ∞`), `Filter.Tendsto.comp`,
`tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `squeeze_zero'`, `Tendsto.eventually_le_const`,
`(tendsto_order.1 hPNT).2` to get `∀ᶠ x, ψ x / x < 1 + δ`.
Suggested structure: (1) a real-analysis lemma `log D_n ≤ 11 ψ(n) + E(n)` with explicit
`E(n) = O(√n log n)`; (2) PNT ⇒ `log D_n ≤ (11 + 12δ) n` eventually; (3) the exponential decay.

**Numerical check.** `python/mirror.py`, section "Stmt_Asymptotic": slope `≈ -0.09 = 11 - 16 log 2`
from `m ≈ 17` on (with exact `ψ, θ`); positive for small `m` (so only the limit statement is true).

**Status: fully proved (`#print axioms` gives `propext, Classical.choice, Quot.sound`).**
The formal proof follows the plan above, with two simplifications:
* `ψ - θ ≤ C √x` (`Chebyshev.psi_sub_theta_le_mul_sqrt`, Costa Pereira) replaces
  `2 √x log x`, so every error term is `O(√n)`:
  `log D_n ≤ 11 ψ(n) + C √n + log 4 · (10 + √(2n))` (`asym_log_Dn_le`), using
  `log Φ_n = ∑ log p` and `θ(n) ≤ log Φ_n + θ(10 + ⌊√(2n)⌋)`;
* `log(n+1) ≤ 2 √n` and `√(2n) ≤ 2 √n` are elementary. With `ψ(n) ≤ (1 + 1/400) n`
  (PNT) and `16 log 2 > 11.0903`, one gets
  `log (D_n (n+1)^B / 2^{16n}) ≤ -n/50` once `n ≥ max(700, (50K)²)`, `K = |C| + 2 log 4 + 2B`
  (`asym_key`). The quantity of the statement is `Cst / 2^14 · D_n (n+1)^{A+11} / 2^{16n}` at
  `n = 2^m - 1` (`asym_rewrite`), which gives the result since `2^m - 1 → ∞`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-! ### Step 1: `log D_n ≤ 11 ψ(n) + C √n + log 4 · (10 + √(2n))` -/

/-- `log Φ_n = ∑_{p ≤ n prime, p ≥ 11, p² > 2n} log p`. -/
private lemma asym_log_Phi (n : ℕ) :
    Real.log (Phi n : ℝ) =
      ∑ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ 11 ≤ p ∧ 2 * n < p ^ 2),
        Real.log (p : ℝ) := by
  unfold Phi
  push_cast
  rw [Real.log_prod]
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact_mod_cast hp.2.1.ne_zero

/-- `θ(n) ≤ log Φ_n + log 4 · (10 + √(2n))`: the primes `≤ n` missing from `Φ_n` are `≤ 10` or
`≤ √(2n)`, so they are all `≤ 10 + ⌊√(2n)⌋`, and Chebyshev's `θ(x) ≤ x log 4` applies. -/
private lemma asym_theta_le (n : ℕ) :
    Chebyshev.theta n ≤ Real.log (Phi n : ℝ) + Real.log 4 * (10 + Real.sqrt (2 * n)) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, asym_log_Phi,
    ← Finset.sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p => 11 ≤ p ∧ 2 * n < p ^ 2)]
  have hS : (Nat.primesLE n).filter (fun p => 11 ≤ p ∧ 2 * n < p ^ 2) =
      (range (n + 1)).filter (fun p => p.Prime ∧ 11 ≤ p ∧ 2 * n < p ^ 2) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨by omega, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h2⟩, h3⟩
  rw [hS]
  have hT : ∑ p ∈ (Nat.primesLE n).filter (fun p => ¬ (11 ≤ p ∧ 2 * n < p ^ 2)), Real.log (p : ℝ)
      ≤ Real.log 4 * (10 + Real.sqrt (2 * n)) := by
    calc ∑ p ∈ (Nat.primesLE n).filter (fun p => ¬ (11 ≤ p ∧ 2 * n < p ^ 2)), Real.log (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE (10 + Nat.sqrt (2 * n)), Real.log (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [Finset.mem_filter, Nat.mem_primesLE] at hp ⊢
            refine ⟨?_, hp.1.2⟩
            by_cases h11 : 11 ≤ p
            · have h2 : p ^ 2 ≤ 2 * n := by
                by_contra h
                exact hp.2 ⟨h11, not_le.mp h⟩
              have := Nat.le_sqrt'.2 h2
              omega
            · omega
          · intro p _ _
            exact Real.log_natCast_nonneg p
      _ = Chebyshev.theta ((10 + Nat.sqrt (2 * n) : ℕ) : ℝ) :=
          (Chebyshev.theta_eq_sum_primesLE_log _).symm
      _ ≤ Real.log 4 * ((10 + Nat.sqrt (2 * n) : ℕ) : ℝ) :=
          Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ Real.log 4 * (10 + Real.sqrt (2 * n)) := by
          have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          have hs : ((Nat.sqrt (2 * n) : ℕ) : ℝ) ≤ Real.sqrt ((2 * n : ℕ) : ℝ) :=
            Real.nat_sqrt_le_real_sqrt
          push_cast at hs ⊢
          gcongr
  linarith

/-- `log D_n ≤ 11 ψ(n) + C √n + log 4 · (10 + √(2n))`, where `C` bounds `ψ - θ` by `C √x`. -/
private lemma asym_log_Dn_le (n : ℕ) (C : ℝ)
    (hC : ∀ x, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    Real.log (Dn n : ℝ) ≤
      11 * Chebyshev.psi n + C * Real.sqrt n + Real.log 4 * (10 + Real.sqrt (2 * n)) := by
  have h1 : (Dn n : ℝ) * (Phi n : ℝ) = (dn n : ℝ) ^ 12 := by exact_mod_cast Dn_mul_Phi n
  have hD : (0 : ℝ) < Dn n := by exact_mod_cast Dn_pos n
  have hP : (0 : ℝ) < Phi n := by exact_mod_cast Phi_pos n
  have h2 : Real.log (Dn n : ℝ) + Real.log (Phi n : ℝ) = 12 * Chebyshev.psi n := by
    rw [← Real.log_mul hD.ne' hP.ne', h1, Real.log_pow, Chebyshev.psi_eq_log_lcmUpto]
    unfold dn
    push_cast
    ring
  have h3 := asym_theta_le n
  have h4 := hC n
  linarith

/-! ### Step 2: PNT gives `ψ(n) ≤ (1 + δ) n` eventually -/

private lemma asym_psi_le (hPNT : PNT_Stmt) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, Chebyshev.psi n ≤ (1 + δ) * n := by
  have h1 : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x / x < 1 + δ :=
    (tendsto_order.1 hPNT).2 _ (by linarith)
  have h2 : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have h4 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (h1.and h2)
  filter_upwards [h4] with n hn
  obtain ⟨hn1, hn2⟩ := hn
  rw [div_lt_iff₀ hn2] at hn1
  linarith

/-! ### Step 3: elementary bounds on the error terms -/

private lemma asym_log_succ_le (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ 2 * Real.sqrt n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 h1
  have h3 := Real.log_le_sub_one_of_pos h2
  rw [Real.log_sqrt h1.le] at h3
  have h4 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt n + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt hn
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  linarith

private lemma asym_sqrt_two_mul_le (n : ℕ) : Real.sqrt (2 * n) ≤ 2 * Real.sqrt n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt hn
  nlinarith

/-! ### Step 4: `D_n (n+1)^B / 2^{16n} → 0` -/

private lemma asym_key (hPNT : PNT_Stmt) (B : ℕ) :
    Tendsto (fun n : ℕ => (Dn n : ℝ) * ((n : ℝ) + 1) ^ B / (2 : ℝ) ^ (16 * n)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set K : ℝ := |C| + 2 * Real.log 4 + 2 * B with hK
  have hK0 : 0 ≤ K := by positivity
  have hψ := asym_psi_le hPNT (δ := 1 / 400) (by norm_num)
  have hbig : ∀ᶠ n : ℕ in atTop, (50 * K) ^ 2 ≤ (n : ℝ) ∧ (700 : ℝ) ≤ n := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (this.eventually_ge_atTop _).and (this.eventually_ge_atTop _)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (Dn n : ℝ) * ((n : ℝ) + 1) ^ B / (2 : ℝ) ^ (16 * n) ≤ Real.exp (-((n : ℝ) / 50)) := by
    filter_upwards [hψ, hbig] with n hψn hn
    obtain ⟨hn1, hn2⟩ := hn
    have hDpos : (0 : ℝ) < Dn n := by exact_mod_cast Dn_pos n
    have hnum : (0 : ℝ) < (Dn n : ℝ) * ((n : ℝ) + 1) ^ B := by positivity
    have hpos : 0 < (Dn n : ℝ) * ((n : ℝ) + 1) ^ B / (2 : ℝ) ^ (16 * n) := by positivity
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    rw [Real.log_div hnum.ne' (by positivity), Real.log_mul hDpos.ne' (by positivity),
      Real.log_pow, Real.log_pow]
    have hlogD := asym_log_Dn_le n C hC
    have hlog1 := asym_log_succ_le n
    have hsq2 := asym_sqrt_two_mul_le n
    have hsqn : 50 * K ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).2 hn1
    have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hA : Real.log 4 * Real.sqrt (2 * n) ≤ Real.log 4 * (2 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hsq2 hl4pos
    have hB : (B : ℝ) * Real.log ((n : ℝ) + 1) ≤ (B : ℝ) * (2 * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg B)
    have hC' : C * Real.sqrt n ≤ |C| * Real.sqrt n :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hs0
    have hKs : K * Real.sqrt n ≤ n / 50 := by nlinarith
    have h16 : (0.6931471803 : ℝ) * n ≤ Real.log 2 * n :=
      mul_le_mul_of_nonneg_right hl2.le (Nat.cast_nonneg n)
    rw [hK] at hKs
    push_cast
    nlinarith
  exact squeeze_zero' (Eventually.of_forall fun n => by positivity) hbound
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)))

/-! ### Step 5: the statement along `n = 2^m - 1` -/

private lemma asym_rewrite (Cst : ℝ) (A m : ℕ) :
    (Dn (2 ^ m - 1) : ℝ) * archBound Cst A (2 ^ m - 1) * (2 : ℝ) ^ (-target m) =
      Cst / 2 ^ 14 * ((Dn (2 ^ m - 1) : ℝ) * (((2 ^ m - 1 : ℕ) : ℝ) + 1) ^ (A + 11) /
        (2 : ℝ) ^ (16 * (2 ^ m - 1))) := by
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 : (((2 ^ m - 1 : ℕ) : ℝ)) + 1 = 2 ^ m := by
    rw [Nat.cast_sub h1m]
    push_cast
    ring
  have ht : -target m = ((11 * m : ℕ) : ℤ) - ((14 + 32 * (2 ^ m - 1) : ℕ) : ℤ) := by
    unfold target
    push_cast [Nat.cast_sub h1m]
    ring
  rw [ht, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  unfold archBound
  rw [h1]
  set n := 2 ^ m - 1 with hn
  have e1 : (2 : ℝ) ^ (16 * n) = ((2 : ℝ) ^ n) ^ 16 := by rw [mul_comm, pow_mul]
  have e2 : (2 : ℝ) ^ (14 + 32 * n) = 2 ^ 14 * ((2 : ℝ) ^ n) ^ 32 := by
    rw [pow_add, mul_comm 32, pow_mul]
  have e3 : (2 : ℝ) ^ (11 * m) = ((2 : ℝ) ^ m) ^ 11 := by rw [mul_comm, pow_mul]
  rw [e1, e2, e3]
  have hy : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  ring

theorem Asymptotic_proof : Stmt_Asymptotic := by
  intro hPNT Cst A
  have hkey := asym_key hPNT (A + 11)
  have hmap : Tendsto (fun m : ℕ => 2 ^ m - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h := (hkey.comp hmap).const_mul (Cst / 2 ^ 14)
  rw [mul_zero] at h
  refine h.congr (fun m => ?_)
  rw [asym_rewrite Cst A m]
  rfl

end Zeta2

end
