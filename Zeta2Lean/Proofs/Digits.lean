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

theorem Digit_proof : Stmt_Digit := by
  sorry

end Zeta2

end
