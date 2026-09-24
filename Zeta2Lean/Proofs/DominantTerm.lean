import Zeta2Lean.Statements

/-!
# The dominant term (proof.md §7 "Dominant term"; Lai (6.3), (6.5))

**Status: proved completely** (`#print axioms L5Dom_proof` = `propext, Classical.choice, Quot.sound`).

**Task.** Prove `Stmt_L5Dom` from `Stmt_Delta`, `Stmt_DeltaFun`, `Stmt_Digit`: for `m ≥ 2`,
(i) `DeltaGe m (target m + 2) domTerm`, and
(ii) `‖volkenbornSum domTerm m‖ = 2^{-target m}`, `target m = 32n + 14 - 11m`, `n = 2^m - 1`.

**Informal proof.** `domTerm m x = K · Φ(x)` with
`K = -336 · 2^{24n+8} · n!^6 · W^2` (`W = (k₀-1)!(n-k₀)!`, `k₀ = 2^{m-1}`) and
`Φ = C(x+n,n)^6 · Y_{k₀}(x)^2 · h₀(x)`,
`Y_{k₀}(x) = C(x+k₀-1, k₀-1) · C(x+n, k₀-1)` (note `n - k₀ = k₀ - 1 = 2^{m-1} - 1`).
`v₂(K) = 4 + 24n + 8 + 6(n-m) + 2(n+1-2m) = 32n + 14 - 10m` exactly (`336 = 2^4 · 21`,
`Digit.fact`, `Digit.dom`).
(i) `Φ = (C(x+n,n)^2)^3 · C(x+k₀-1,k₀-1)^2 · C(x+n,k₀-1)^2 · h₀`: `Δ_m(C(x+n,n)^2) ≥ 1-(m-1) = 2-m`
(`DeltaFun.binomSq`, `Nat.log 2 n = m-1 < m`); `Δ(C(·, k₀-1)) ≥ -(m-2)` (`Nat.log 2 (2^{m-1}-1) = m-2`);
`Δ(h₀) ≥ 0`; all `ℤ₂`-valued, so `Δ_m(Φ) ≥ 2 - m` (`Delta.mul`, `Delta.ofAll`, `Delta.mono`) and
`Δ_m(domTerm) ≥ 32n + 14 - 10m + 2 - m = target + 2` (`Delta.smul`).
(ii) `volkenbornSum domTerm m = 2^{-m} K ∑_{x<2^m} Φ(x)`.  `Φ(0) = C(n, k₀-1)^2 h₀(0)` is a
2-adic unit: `C(2^m - 1, j)` is odd for `j ≤ 2^m - 1` (no carries: Kummer/Lucas) and
`h₀(0) = ∏_{k≤n} (2k+1)^{-8}`.  For `1 ≤ x ≤ 2^m - 1`, `C(x + 2^m - 1, 2^m - 1)` is even (adding `x`
and `2^m - 1` in base 2 carries), so `‖Φ(x)‖ ≤ 1/2` (in fact `≤ 2^{-6}`).  Ultrametric:
`‖∑_{x<2^m} Φ(x)‖ = 1`, hence `‖volkenbornSum domTerm m‖ = 2^m · 2^{-(32n+14-10m)} = 2^{-target m}`.

**How the Lean proof goes.**
* `dtK m` is the rational constant `K`; `dt_padicValRat_K` computes `v₂(K) = target m + m` from
  `padicValRat.mul/neg/pow/of_nat`, `v₂(336) = 4`, `hG.fact m`, `hG.dom m`; `dt_norm_K` turns it
  into `‖K‖ = 2^{-(target m + m)}` (`Padic.eq_padicNorm`, `padicNorm.eq_zpow_of_nonzero`).
* `dtPhi m x` is `Φ` written as the product of 8 factors
  `B^2 · B^2 · B^2 · Y1 · Y1 · Y2 · Y2 · H` (`B = C(x+n,n)`, `Y1 = C(x+(k₀-1),k₀-1)`,
  `Y2 = C(x+n,k₀-1)`, `H = h₀`), and `dt_domTerm_eq` shows `domTerm m x = K · Φ(x)` (after the
  ℕ-rewrites `x + k₀ - 1 = x + (k₀ - 1)`, `2^m - 1 - 2^{m-1} = 2^{m-1} - 1`).
* (i) every factor is `IntValued` with `DeltaGe m (2 - m)` (`hF.binomSq`, `hF.binom` + `hD.ofAll`,
  `hF.hcoefDelta` + `hD.monoAll` + `hD.ofAll`); `hD.mul` 7 times, then `hD.smul` with `e = target + m`.
* (ii) `C(2^m-1, j)` is odd by Lucas (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`, induction
  on `m`); `C(x+2^m-1, 2^m-1)` is even for `1 ≤ x < 2^m` because
  `C(x+n,n) · x = C(x+n,n+1) · 2^m` (`Nat.choose_succ_right_eq`) and `2^m ∤ x`;
  `h₀(x) = ∏_k (2x+2k+1)^{-8}` has norm `1` (`PowerSeries.constantCoeff_inv`).  Then
  `Finset.sum_range_succ'` + `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` give
  `‖∑_{x<2^m} Φ(x)‖ = 1`.

**Numerical check.** `python/mirror.py`, section "Stmt_L5Dom": `v₂(R_m(domTerm)) = target m` for
`m = 2..5`, and the `Δ_m` bound on `k < 2^{m+4}`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### Elementary facts about binomial coefficients and 2-adic norms -/

/-- `⌊log₂ (2^k - 1)⌋ = k - 1` for `k ≥ 1`. -/
private lemma dt_log_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) : Nat.log 2 (2 ^ k - 1) = k - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by rw [pow_succ]; omega⟩)]
  simp only [Nat.add_sub_cancel, pow_succ]
  omega

/-- `C(2^m - 1, j)` is odd for `j ≤ 2^m - 1` (Lucas; induction on `m`). -/
private lemma dt_choose_odd (m : ℕ) : ∀ j, j ≤ 2 ^ m - 1 → Nat.choose (2 ^ m - 1) j % 2 = 1 := by
  induction m with
  | zero => intro j hj; simp at hj; subst hj; simp
  | succ m ih =>
    intro j hj
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have hn : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by rw [pow_succ]; omega
    have hL :=
      @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 ^ (m + 1) - 1) j 2 ⟨Nat.prime_two⟩
    rw [hn] at hL hj
    have e1 : (2 * (2 ^ m - 1) + 1) % 2 = 1 := by omega
    have e2 : (2 * (2 ^ m - 1) + 1) / 2 = 2 ^ m - 1 := by omega
    rw [e1, e2] at hL
    have hj2 : j / 2 ≤ 2 ^ m - 1 := by omega
    have hc : Nat.choose 1 (j % 2) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one j with h | h <;> rw [h] <;> rfl
    rw [hn]
    unfold Nat.ModEq at hL
    rw [hL, hc, one_mul]
    exact ih _ hj2

/-- `C(x + 2^m - 1, 2^m - 1)` is even for `1 ≤ x < 2^m`: `C(x+n,n) · x = C(x+n,n+1) · 2^m`
(`n = 2^m - 1`) and `2^m ∤ x`. -/
private lemma dt_choose_even (m x : ℕ) (hx1 : 1 ≤ x) (hx2 : x < 2 ^ m) :
    2 ∣ Nat.choose (x + (2 ^ m - 1)) (2 ^ m - 1) := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have key := Nat.choose_succ_right_eq (x + (2 ^ m - 1)) (2 ^ m - 1)
  have e1 : 2 ^ m - 1 + 1 = 2 ^ m := by omega
  have e2 : x + (2 ^ m - 1) - (2 ^ m - 1) = x := by omega
  rw [e1, e2] at key
  by_contra hc
  have hodd : Nat.Coprime (2 ^ m) (Nat.choose (x + (2 ^ m - 1)) (2 ^ m - 1)) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  have hdvd : 2 ^ m ∣ Nat.choose (x + (2 ^ m - 1)) (2 ^ m - 1) * x :=
    ⟨_, by rw [← key, mul_comm]⟩
  have := Nat.le_of_dvd hx1 (hodd.dvd_of_dvd_mul_left hdvd)
  omega

private lemma dt_norm_two : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := @Padic.norm_p 2 ⟨Nat.prime_two⟩
  simpa using this

private lemma dt_norm_nat_le (a : ℕ) : ‖(a : ℚ_[2])‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one ℚ_[2] a

private lemma dt_norm_even (a : ℕ) (h : 2 ∣ a) : ‖(a : ℚ_[2])‖ ≤ 1 / 2 := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  rw [norm_mul, dt_norm_two]
  have := dt_norm_nat_le c
  linarith

private lemma dt_norm_odd (a : ℕ) (h : a % 2 = 1) : ‖(a : ℚ_[2])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h))

/-- `h₀(x) = ∏_{k ≤ n} (2x+2k+1)^{-8}`. -/
private lemma dt_hcoef_zero (n x : ℕ) :
    hcoef n 0 x = ∏ k ∈ range (n + 1), ((((2 * x + 2 * k + 1 : ℕ) : ℚ)) ^ 8)⁻¹ := by
  unfold hcoef
  rw [coeff_zero_eq_constantCoeff_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [constantCoeff_inv]
  simp

/-- `h₀(x)` is a 2-adic unit. -/
private lemma dt_norm_hcoef_zero (n x : ℕ) : ‖((hcoef n 0 x : ℚ) : ℚ_[2])‖ = 1 := by
  rw [dt_hcoef_zero, Rat.cast_prod, norm_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, norm_inv, norm_pow, dt_norm_odd _ (by omega)]
  simp

private lemma dt_norm_rat (q : ℚ) (hq : q ≠ 0) :
    ‖(q : ℚ_[2])‖ = (2 : ℝ) ^ (-padicValRat 2 q) := by
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hq]
  push_cast
  rfl

/-! ### The constant `K` and its exact valuation -/

/-- The constant factor `K = -336 · 2^{24n+8} · n!^6 · W^2` of `domTerm`. -/
private def dtK (m : ℕ) : ℚ :=
  -336 * (2 : ℚ) ^ (24 * (2 ^ m - 1) + 8) * (((2 ^ m - 1).factorial : ℕ) : ℚ) ^ 6 *
    ((Wl (2 ^ m - 1) (2 ^ (m - 1)) : ℕ) : ℚ) ^ 2

private lemma dt_padicValNat_336 : padicValNat 2 336 = 4 := by
  have : (336 : ℕ) = 2 ^ 4 * 21 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
  simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 21 by decide)]

/-- `v₂(K) = 32n + 14 - 10m = target m + m`. -/
private lemma dt_padicValRat_K (hG : Stmt_Digit) (m : ℕ) (hm : 2 ≤ m) :
    padicValRat 2 (dtK m) = target m + m := by
  have hfact := hG.fact m
  have hdom := hG.dom m hm
  have hF0 : (((2 ^ m - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hW0 : ((Wl (2 ^ m - 1) (2 ^ (m - 1)) : ℕ) : ℚ) ≠ 0 := by
    unfold Wl
    exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  have h336 : padicValRat 2 (336 : ℚ) = 4 := by
    have : (336 : ℚ) = ((336 : ℕ) : ℚ) := by norm_num
    rw [this, padicValRat.of_nat, dt_padicValNat_336]
    norm_num
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using @padicValRat.self 2 (by norm_num)
  unfold dtK
  rw [padicValRat.mul (by positivity) (pow_ne_zero _ hW0),
    padicValRat.mul (by positivity) (pow_ne_zero _ hF0),
    padicValRat.mul (by norm_num) (by positivity), padicValRat.neg, padicValRat.pow,
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat, h336, h2]
  unfold Wl at *
  rw [hfact, hdom]
  have h1 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h3 : m ≤ 2 ^ (m - 1) := by
    have := @Nat.lt_two_pow_self (m - 1)
    omega
  have h4 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hPZ : ((2 : ℤ)) ^ m = ((2 ^ m : ℕ) : ℤ) := by norm_num
  unfold target
  rw [hPZ]
  generalize 2 ^ (m - 1) = Q at *
  generalize 2 ^ m = P at *
  push_cast
  omega

/-- `‖K‖ = 2^{-(target m + m)}`. -/
private lemma dt_norm_K (hG : Stmt_Digit) (m : ℕ) (hm : 2 ≤ m) :
    ‖((dtK m : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(target m + m)) := by
  have hK0 : dtK m ≠ 0 := by
    unfold dtK Wl
    have := Nat.factorial_pos (2 ^ m - 1)
    have := Nat.factorial_pos (2 ^ (m - 1) - 1)
    have := Nat.factorial_pos (2 ^ m - 1 - 2 ^ (m - 1))
    positivity
  rw [dt_norm_rat _ hK0, dt_padicValRat_K hG m hm]

/-! ### The function part `Φ` of `domTerm` -/

/-- `C(x+n, n)`, `n = 2^m - 1`. -/
private def dtB (m x : ℕ) : ℚ_[2] := ((Nat.choose (x + (2 ^ m - 1)) (2 ^ m - 1) : ℕ) : ℚ_[2])

/-- `C(x+k₀-1, k₀-1)`, `k₀ = 2^{m-1}`. -/
private def dtY1 (m x : ℕ) : ℚ_[2] :=
  ((Nat.choose (x + (2 ^ (m - 1) - 1)) (2 ^ (m - 1) - 1) : ℕ) : ℚ_[2])

/-- `C(x+n, k₀-1)`. -/
private def dtY2 (m x : ℕ) : ℚ_[2] :=
  ((Nat.choose (x + (2 ^ m - 1)) (2 ^ (m - 1) - 1) : ℕ) : ℚ_[2])

/-- `h₀(x)`. -/
private def dtH (m x : ℕ) : ℚ_[2] := ((hcoef (2 ^ m - 1) 0 x : ℚ) : ℚ_[2])

/-- `Φ = C(x+n,n)^6 · C(x+k₀-1,k₀-1)^2 · C(x+n,k₀-1)^2 · h₀`, as a product of 8 factors. -/
private def dtPhi (m x : ℕ) : ℚ_[2] :=
  dtB m x ^ 2 * dtB m x ^ 2 * dtB m x ^ 2 * dtY1 m x * dtY1 m x * dtY2 m x * dtY2 m x * dtH m x

/-- `domTerm m x = K · Φ(x)`. -/
private lemma dt_domTerm_eq (m : ℕ) (hm : 2 ≤ m) (x : ℕ) :
    ((domTerm m x : ℚ) : ℚ_[2]) = ((dtK m : ℚ) : ℚ_[2]) * dtPhi m x := by
  have hk1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e1 : x + 2 ^ (m - 1) - 1 = x + (2 ^ (m - 1) - 1) := Nat.add_sub_assoc hk1 x
  have e2 : 2 ^ m - 1 - 2 ^ (m - 1) = 2 ^ (m - 1) - 1 := by omega
  unfold domTerm dtK dtPhi dtB dtY1 dtY2 dtH Bn Yl
  rw [e1, e2]
  push_cast
  ring

/-! ### Part (i): `Δ_m(Φ) ≥ 2 - m` -/

private lemma dt_pair_mul (hD : Stmt_Delta) {m : ℕ} {c : ℤ} {f g : ℕ → ℚ_[2]}
    (hf : IntValued f ∧ DeltaGe m c f) (hg : IntValued g ∧ DeltaGe m c g) :
    IntValued (fun x => f x * g x) ∧ DeltaGe m c (fun x => f x * g x) := by
  refine ⟨fun x => ?_, hD.mul f g m c hf.1 hg.1 hf.2 hg.2⟩
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ 1 * 1 := mul_le_mul (hf.1 x) (hg.1 x) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

private lemma dt_B_sq (hF : Stmt_DeltaFun) (m : ℕ) (hm : 2 ≤ m) :
    IntValued (fun x => dtB m x ^ 2) ∧ DeltaGe m (2 - m) (fun x => dtB m x ^ 2) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (dt_norm_nat_le _)
  · have hlog : Nat.log 2 (2 ^ m - 1) = m - 1 := dt_log_two_pow_sub_one m (by omega)
    have := hF.binomSq (2 ^ m - 1) (2 ^ m - 1) m (by omega)
    rw [hlog, show (1 : ℤ) - ((m - 1 : ℕ) : ℤ) = 2 - m by omega] at this
    exact this

private lemma dt_Y1 (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (m : ℕ) (hm : 2 ≤ m) :
    IntValued (dtY1 m) ∧ DeltaGe m (2 - m) (dtY1 m) := by
  refine ⟨fun x => dt_norm_nat_le _, ?_⟩
  have hlog : Nat.log 2 (2 ^ (m - 1) - 1) = m - 2 := by
    rw [dt_log_two_pow_sub_one (m - 1) (by omega)]
    omega
  have := hF.binom (2 ^ (m - 1) - 1) (2 ^ (m - 1) - 1)
  rw [hlog, show -((m - 2 : ℕ) : ℤ) = 2 - m by omega] at this
  exact hD.ofAll _ m _ this

private lemma dt_Y2 (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (m : ℕ) (hm : 2 ≤ m) :
    IntValued (dtY2 m) ∧ DeltaGe m (2 - m) (dtY2 m) := by
  refine ⟨fun x => dt_norm_nat_le _, ?_⟩
  have hlog : Nat.log 2 (2 ^ (m - 1) - 1) = m - 2 := by
    rw [dt_log_two_pow_sub_one (m - 1) (by omega)]
    omega
  have := hF.binom (2 ^ m - 1) (2 ^ (m - 1) - 1)
  rw [hlog, show -((m - 2 : ℕ) : ℤ) = 2 - m by omega] at this
  exact hD.ofAll _ m _ this

private lemma dt_H (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (m : ℕ) (hm : 2 ≤ m) :
    IntValued (dtH m) ∧ DeltaGe m (2 - m) (dtH m) :=
  ⟨hF.hcoefInt (2 ^ m - 1) 0,
    hD.ofAll _ m _ (hD.monoAll _ 0 (2 - m) (by omega) (hF.hcoefDelta (2 ^ m - 1) 0))⟩

private lemma dt_Phi_delta (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (m : ℕ) (hm : 2 ≤ m) :
    DeltaGe m (2 - m) (dtPhi m) := by
  have hB := dt_B_sq hF m hm
  have h1 := dt_Y1 hD hF m hm
  have h2 := dt_Y2 hD hF m hm
  have hH := dt_H hD hF m hm
  exact (dt_pair_mul hD (dt_pair_mul hD (dt_pair_mul hD (dt_pair_mul hD (dt_pair_mul hD
    (dt_pair_mul hD (dt_pair_mul hD hB hB) hB) h1) h1) h2) h2) hH).2

/-! ### Part (ii): the level-`m` Riemann sum of `Φ` is a 2-adic unit times `2^{-m}` -/

/-- `Φ(0) = C(n, k₀-1)^2 h₀(0)` is a 2-adic unit. -/
private lemma dt_Phi_zero (m : ℕ) (hm : 2 ≤ m) : ‖dtPhi m 0‖ = 1 := by
  have hk1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hB : dtB m 0 = 1 := by simp [dtB]
  have hY1 : dtY1 m 0 = 1 := by simp [dtY1]
  have hY2 : ‖dtY2 m 0‖ = 1 := by
    unfold dtY2
    rw [zero_add]
    exact dt_norm_odd _ (dt_choose_odd m _ (by omega))
  have hH : ‖dtH m 0‖ = 1 := dt_norm_hcoef_zero _ _
  unfold dtPhi
  simp only [norm_mul, norm_pow, hB, hY1, hY2, hH, norm_one]
  norm_num

/-- `‖Φ(x)‖ ≤ 1/2` for `1 ≤ x < 2^m` (because `C(x+n, n)` is even). -/
private lemma dt_Phi_pos (m : ℕ) (x : ℕ) (hx1 : 1 ≤ x) (hx2 : x < 2 ^ m) :
    ‖dtPhi m x‖ ≤ 1 / 2 := by
  have hB : ‖dtB m x‖ ≤ 1 / 2 := dt_norm_even _ (dt_choose_even m x hx1 hx2)
  have hB1 : ‖dtB m x‖ ≤ 1 := dt_norm_nat_le _
  have hY1 : ‖dtY1 m x‖ ≤ 1 := dt_norm_nat_le _
  have hY2 : ‖dtY2 m x‖ ≤ 1 := dt_norm_nat_le _
  have hH : ‖dtH m x‖ ≤ 1 := by
    unfold dtH
    rw [dt_norm_hcoef_zero]
  unfold dtPhi
  simp only [norm_mul, norm_pow]
  calc ‖dtB m x‖ ^ 2 * ‖dtB m x‖ ^ 2 * ‖dtB m x‖ ^ 2 * ‖dtY1 m x‖ * ‖dtY1 m x‖ *
        ‖dtY2 m x‖ * ‖dtY2 m x‖ * ‖dtH m x‖ ≤ (1 / 2) ^ 2 * 1 ^ 2 * 1 ^ 2 * 1 * 1 * 1 * 1 * 1 := by
        gcongr
    _ ≤ 1 / 2 := by norm_num

/-- `‖∑_{x < 2^m} Φ(x)‖ = 1` (ultrametric: `Φ(0)` is a unit, all other terms are `≤ 1/2`). -/
private lemma dt_norm_sum (m : ℕ) (hm : 2 ≤ m) : ‖∑ x ∈ range (2 ^ m), dtPhi m x‖ = 1 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ m = N + 1 := ⟨2 ^ m - 1, by omega⟩
  rw [hN, Finset.sum_range_succ']
  have h0 : ‖dtPhi m 0‖ = 1 := dt_Phi_zero m hm
  have hrest : ‖∑ i ∈ range N, dtPhi m (i + 1)‖ ≤ 1 / 2 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact dt_Phi_pos m (i + 1) (by omega) (by omega)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h0]; linarith), h0]
  exact max_eq_right (by linarith)

/-! ### The theorem -/

theorem L5Dom_proof (hD : Stmt_Delta) (hF : Stmt_DeltaFun) (hG : Stmt_Digit) : Stmt_L5Dom := by
  intro m hm
  have hfun : (fun x => ((domTerm m x : ℚ) : ℚ_[2])) =
      fun x => ((dtK m : ℚ) : ℚ_[2]) * dtPhi m x := funext (dt_domTerm_eq m hm)
  rw [hfun]
  constructor
  · -- (i) `Δ_m(K Φ) ≥ (2 - m) + v₂(K) = target m + 2`
    have := hD.smul (dtPhi m) m (2 - m) (target m + m) _ (le_of_eq (dt_norm_K hG m hm))
      (dt_Phi_delta hD hF m hm)
    rw [show (2 - (m : ℤ)) + (target m + m) = target m + 2 by ring] at this
    exact this
  · -- (ii) `‖2^{-m} K ∑ Φ‖ = 2^m · 2^{-(target m + m)} · 1`
    rw [volkenbornSum_const_mul, norm_mul, dt_norm_K hG m hm]
    unfold volkenbornSum
    rw [norm_mul, norm_inv, norm_pow, dt_norm_two, dt_norm_sum m hm, mul_one, one_div, inv_pow,
      inv_inv, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    congr 1
    ring

end Zeta2

end
