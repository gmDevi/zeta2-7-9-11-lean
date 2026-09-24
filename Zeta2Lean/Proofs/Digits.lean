import Zeta2Lean.Statements

/-!
# Lai's digit lemma (proof.md P7; Lai arXiv:2304.00816, Lemma 6.1)

**Task.** Prove the three fields of `Stmt_Digit` (`n = 2^m - 1`, `k₀ = 2^{m-1}`):
* `fact : v₂(n!) = 2^m - 1 - m`;
* `dom : v₂((k₀-1)! (n-k₀)!) = 2^m - 2m`  (`m ≥ 2`);
* `other : v₂((l-1)! (n-l)!) ≥ 2^m + 1 - 2m`  for `1 ≤ l ≤ n`, `l ≠ k₀`  (`m ≥ 2`).
No hypotheses.

**Informal proof.** Legendre: `v₂(a!) = a - s₂(a)`, `s₂` = binary digit sum
(`sub_one_mul_padicValNat_factorial` with `p = 2`).  `s₂(2^m - 1) = m`, giving `fact`.  For
`1 ≤ l ≤ n`: `v₂((l-1)!(n-l)!) = n - 1 - s₂(l-1) - s₂(n-l)`.  Both `l-1, n-l ∈ [0, 2^m - 2]`, and a
number `a` with `s₂(a)` ones is `≥ 2^{s₂(a)} - 1`, so `s₂(a) ≤ m - 1` for `a ≤ 2^m - 2`; hence the
valuation is `≥ n - 1 - 2(m-1) = 2^m - 2m`.  Equality forces `s₂(l-1) = s₂(n-l) = m - 1`; since
`min(l-1, n-l) ≤ 2^{m-1} - 1` and a number `< 2^{m-1}` with `m-1` ones equals `2^{m-1}-1`, we get
`min(l-1, n-l) = 2^{m-1} - 1`, i.e. `l = k₀`.  For `l = k₀`: `k₀ - 1 = n - k₀ = 2^{m-1} - 1`, each
with digit sum `m-1`, giving `dom`.
(Alternative without digit sums: Legendre `v₂(a!) = ∑_{i≥1} ⌊a/2^i⌋` and
`⌊a/2^i⌋ + ⌊b/2^i⌋ ≥ ⌊(a+b)/2^i⌋ - 1` with `a + b = 2^m - 2`, `⌊(2^m-2)/2^i⌋ = 2^{m-i} - 1`.)

**Formal proof (as implemented below).**  Only two facts about the binary digit sum
`s₂(a) = (Nat.digits 2 a).sum` are used:
* `two_pow_digitSum_two_le : 2^{s₂(a)} ≤ a + 1` (strong induction, `Nat.digits_def'`);
* `digitSum_two_pow_sub_one : s₂(2^m - 1) = m` (induction, `Nat.digits_add`).
The equality case needs no digit characterisation: if `s₂(l-1) = s₂(n-l) = m-1` then
`2^{m-1} ≤ (l-1)+1 = l` and `2^{m-1} ≤ (n-l)+1 = 2^m - l`, so `l = 2^{m-1}`.
Everything else is `omega` (with `2^m = 2·2^{m-1}` supplied).

**Lean hints.** `sub_one_mul_padicValNat_factorial : (p-1) * v_p(n!) = n - (p.digits n).sum`,
`padicValNat_factorial`, `padicValNat.mul` (factorials are non-zero: `Nat.factorial_ne_zero`),
`Nat.digits`, `Nat.digits_add_two_add_one`, `Nat.digits_lt_base`, `Nat.length_digits`,
`Nat.ofDigits`, `Nat.ofDigits_digits`, `Nat.digits_base_pow_mul`;
the statement is also amenable to strong induction on `m` using `Nat.log`.  `omega` for the
final arithmetic.

**Numerical check.** `python/mirror.py`, section "Stmt_Digit" (`m ≤ 14`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- Legendre's formula for `p = 2`: `v₂(a!) = a - s₂(a)`, `s₂` the binary digit sum. -/
private lemma digitsPf_padicValNat_two_factorial (a : ℕ) :
    padicValNat 2 a.factorial = a - (Nat.digits 2 a).sum := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) a
  simpa using h

/-- A number whose binary digit sum is `s` is at least `2^s - 1`: `2^{s₂(a)} ≤ a + 1`. -/
private lemma digitsPf_two_pow_digitSum_le (a : ℕ) : 2 ^ (Nat.digits 2 a).sum ≤ a + 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h := ih (a / 2) (Nat.div_lt_self ha (by norm_num))
      rw [Nat.digits_def' (by norm_num) ha, List.sum_cons, pow_add]
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
      · rw [h0, pow_zero, one_mul]
        omega
      · rw [h1, pow_one]
        omega

/-- `s₂(2^m - 1) = m`. -/
private lemma digitsPf_digitSum_two_pow_sub_one (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h : 2 ^ (k + 1) - 1 = 1 + 2 * (2 ^ k - 1) := by
      rw [pow_succ]
      omega
    rw [h, Nat.digits_add 2 (by norm_num) 1 (2 ^ k - 1) (by norm_num) (Or.inl one_ne_zero),
      List.sum_cons, ih]
    omega

/-- `2^m = 2 · 2^{m-1}` for `m ≥ 1`. -/
private lemma digitsPf_two_pow_eq (m : ℕ) (hm : 1 ≤ m) : 2 ^ m = 2 * 2 ^ (m - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem Digit_proof : Stmt_Digit where
  fact m := by
    rw [digitsPf_padicValNat_two_factorial, digitsPf_digitSum_two_pow_sub_one]
  dom m hm := by
    have hK := digitsPf_two_pow_eq m (by omega)
    have h1 : 2 ^ m - 1 - 2 ^ (m - 1) = 2 ^ (m - 1) - 1 := by omega
    have h2 := Nat.digit_sum_le 2 (2 ^ (m - 1) - 1)
    rw [digitsPf_digitSum_two_pow_sub_one] at h2
    rw [h1, padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      digitsPf_padicValNat_two_factorial, digitsPf_digitSum_two_pow_sub_one]
    omega
  other m hm l hl1 hln hlk := by
    have hK := digitsPf_two_pow_eq m (by omega)
    rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      digitsPf_padicValNat_two_factorial, digitsPf_padicValNat_two_factorial]
    have e₁ := digitsPf_two_pow_digitSum_le (l - 1)
    have e₂ := digitsPf_two_pow_digitSum_le (2 ^ m - 1 - l)
    have d₁ := Nat.digit_sum_le 2 (l - 1)
    have d₂ := Nat.digit_sum_le 2 (2 ^ m - 1 - l)
    set s₁ := (Nat.digits 2 (l - 1)).sum
    set s₂ := (Nat.digits 2 (2 ^ m - 1 - l)).sum
    -- both digit sums are `≤ m - 1`, since `2^{s} ≤ 2^m - 1`
    have b₁ : s₁ ≤ m - 1 := by
      by_contra h
      have : 2 ^ m ≤ 2 ^ s₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have b₂ : s₂ ≤ m - 1 := by
      by_contra h
      have : 2 ^ m ≤ 2 ^ s₂ := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    -- they are not both `m - 1`: otherwise `2^{m-1} ≤ l` and `2^{m-1} ≤ 2^m - l`, so `l = 2^{m-1}`
    have hsum : s₁ + s₂ + 3 ≤ 2 * m := by
      by_contra hcon
      have h1 : s₁ = m - 1 := by omega
      have h2 : s₂ = m - 1 := by omega
      rw [h1] at e₁
      rw [h2] at e₂
      omega
    omega

end Zeta2

end
