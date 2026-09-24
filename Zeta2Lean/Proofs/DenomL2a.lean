import Zeta2Lean.Statements

/-!
# L2a: `d_n^{8-i} r_{i,k} ∈ ℤ` (proof.md §4.1)

**Task.** Prove `Stmt_L2a` from `Stmt_BlockF`.

**Informal proof.** Call `A ∈ ℚ⟦X⟧` *`d`-integral* if `∀ j, ∃ z : ℤ, d^j * coeff j A = z`.  This
class is closed under `+`, `*` (Cauchy product `d^j ∑_{a+b=j} A_a B_b = ∑ (d^a A_a)(d^b B_b)`),
powers, and contains `C z` (`z ∈ ℤ`) and `X`.  Take `d = d_n = lcm(1..n)`.  Since
`2^{16n} = (4^n)^8`,
  `Gser n k = (C(n-2k) + 2X) · (4^n Ψ_k)^8`,
  `4^n Ψ_k = [4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k}] · [n! / ((1-ε)_k (1+ε)_{n-k})]`.
The first bracket is `d_n`-integral by `Stmt_BlockF`.  For the second,
`(1-ε)_k = k! ∏_{i=1}^{k} (1 - ε/i)` and `(1+ε)_{n-k} = (n-k)! ∏_{i=1}^{n-k} (1 + ε/i)`, so
  `n!/((1-ε)_k (1+ε)_{n-k}) = C(n,k) ∏_{i=1}^{k} (1-ε/i)⁻¹ ∏_{i=1}^{n-k} (1+ε/i)⁻¹`,
and `(1 ∓ ε/i)⁻¹ = ∑_j (±1/i)^j ε^j` is `d_n`-integral because `i ∣ d_n` (`i ≤ n`).  Hence
`Gser n k` is `d_n`-integral, and `r_{i,k} = coeff (8-i) (Gser n k)` gives the claim.

**Lean hints.** `PowerSeries.coeff_mul`, `Finset.sum_mul_sum`, `Finset.mem_antidiagonal`, `PowerSeries.mk`, `PowerSeries.coeff_mk`,
`PowerSeries.eq_inv_iff_mul_eq_one` (to identify `(1 - ε/i)⁻¹` with a geometric series),
`PowerSeries.mul_inv_rev`, `Finset.prod_range_succ`, `Nat.choose_mul_factorial_mul_factorial`,
`Finset.dvd_lcm`, `Nat.lcmUpto`, `Int.cast_mul`, `Int.cast_sum`.

**Numerical check.** `python/mirror.py`, section "Stmt_BlockF, Stmt_L2a, Stmt_L2b" (`n ≤ 20`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem L2a_proof (hF : Stmt_BlockF) : Stmt_L2a := by
  sorry

end Zeta2

end
