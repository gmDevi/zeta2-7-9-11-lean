import Zeta2Lean.Statements

/-!
# The one-power saving at `ε = 0`: `v_p(F_J(0)) ≥ -4` (proof.md §4.3 Step 5; LSZ (5.4))

**Task.** Prove `Stmt_FJKummer`: for a prime `p ≥ 11` with `p² > 2n`, `1 ≤ ℓ ≤ n`,
`J ∈ chains 8 (n-ℓ)`: `-4 ≤ padicValRat p (FJ0 n ℓ J)`.  No hypotheses (pure number theory on the
explicit formula `FJ0`).

**Informal proof.** Write `N = n - ℓ`.  All binomial coefficients and `N+1` are positive integers
(`v_p ≥ 0`), `-64` is a `p`-unit, and the only denominators are `(2ℓ-1)^4` and `J_8 + 1`, both
integers in `[1, 2n] ⊂ [1, p²)`, hence of valuation `≤ 1`.  So trivially `v_p(FJ0) ≥ -5`, and
`≥ -4` unless `p ∣ 2ℓ-1` **and** `p ∣ J_8+1`, i.e. `ℓ ≡ (p+1)/2`, `J_8 ≡ -1 (mod p)`.
(⋆) Kummer: if `(m mod p) ≥ (p+1)/2` then `p ∣ C(2m, m)` (the lowest base-`p` digit carries in
`m + m`).  Let `x := J_1 mod p`.
* `x ≥ (p+1)/2`: `p ∣ C(2J_1, J_1) = C(2d_1, d_1)` (`d_1 = J_1`).
* `x ≤ (p-3)/2`: `(ℓ + J_1) mod p = (p+1)/2 + x ∈ [(p+1)/2, p-1]`, so `p ∣ C(2(ℓ+J_1), ℓ+J_1)`.
* `x = (p-1)/2`: then `N - J_1 ≡ n - ℓ - J_1 ≡ n (mod p)`.
  - `(n mod p) ≥ (p+1)/2`: `p ∣ C(2(N-J_1), N-J_1)`.
  - `(n mod p) = (p-1)/2`: `N + 1 = n - ℓ + 1 ≡ 0 (mod p)`, so `p ∣ N+1`.
  - `(n mod p) ≤ (p-3)/2`: `N - J_8 ≡ n - (p+1)/2 + 1 ≡ n + (p+1)/2 (mod p)` lies in
    `[(p+1)/2, p-1]` (mod `p`), so `p ∣ C(2(N-J_8), N-J_8)`.
Each of these factors occurs in `FJ0` (the factor `i = 1` of the first and second products, the
factor `i = 1` or `i = 8` of the third product, or `N+1`).  Hence `v_p(FJ0) ≥ -4`.
[The value `-4` is attained; `p ≥ 11` is not needed by this argument — any odd `p` works — but it
is the hypothesis used downstream.]

**Lean hints.** `padicValRat.mul`, `padicValRat.div`, `padicValRat.pow`, `padicValRat_of_nat`,
`padicValNat.eq_zero_of_not_dvd`, `padicValNat_le_nat_log`, `Nat.log_eq_iff`,
`padicValNat_choose : padicValNat p (n.choose k) = #{i ∈ Ico 1 b | p^i ≤ k % p^i + (n-k) % p^i}`
(Kummer; use `b = 2` since `2m < p²`), `Nat.Prime.dvd_choose_add`, `one_le_padicValNat_of_dvd`,
`Nat.mod_add_div`, `Nat.add_mod`, `omega` for the residue bookkeeping,
`Fin.prod_univ_eight`, `Finset.prod_pos`, `Finset.single_le_prod`,
There is no `padicValRat.prod` in Mathlib: prove "`padicValRat` of a product of non-zero factors is
the sum of the valuations" by `Finset` induction with `padicValRat.mul`.  Chain facts:
`mem_chains`, `chainPrev_le` (proved in `Defs.lean`).

**Numerical check.** `python/mirror.py`, section "... Stmt_FJKummer ..." (random critical-biased
samples, `n ≤ 300`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem FJKummer_proof : Stmt_FJKummer := by
  sorry

end Zeta2

end
