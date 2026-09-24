import Zeta2Lean.Statements

/-!
# Building block `F` (proof.md P5; Lai–Yu Lemma 4.2, Zudilin 2004 Lemma 16)

**Task.** Prove `Stmt_BlockF`: for `k ≤ n` and all `j`,
`d_n^j · [ε^j] ( 4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k} ) ∈ ℤ`.  No hypotheses.

**Informal proof.** Write `binom(z, a) := z(z-1)⋯(z-a+1)/a!` (a polynomial in `z`; Mathlib's
`Ring.choose`, or `(descPochhammer ℚ a).eval z / a!`).  Reindexing,
  `(1/2-ε)_k (1/2+ε)_{n-k} = (-1)^k (1/2-k+ε)_n = (-1)^k n! · binom(ε + t - 1/2, n)`,  `t := n - k`.
Vandermonde twice (`binom(x+y+z, n) = ∑_{a+b+c=n} binom(x,a) binom(y,b) binom(z,c)`) with
`x = ε`, `y = t ∈ ℕ`, `z = -1/2`, and `binom(-1/2, c) = (-1)^c C(2c,c) / 4^c`, gives
  `4^n/n! · (1/2-ε)_k (1/2+ε)_{n-k} = (-1)^k ∑_{a+b+c=n} 4^{a+b} C(t,b) (-1)^c C(2c,c) · binom(ε, a)`.
All coefficients `4^{a+b} C(t,b) (-1)^c C(2c,c)` are integers.  Finally, for `a ≤ n`,
`binom(ε, a) = (-1)^{a-1} (ε/a) ∏_{i=1}^{a-1} (1 - ε/i)` (for `a ≥ 1`; `binom(ε,0) = 1`), so
`[ε^j] binom(ε, a) = ± e_{j-1}(1/1, …, 1/(a-1)) / a` is a sum of terms `±1/(a i₁ ⋯ i_{j-1})` with
all factors `≤ n`, and `d_n^j / (a i₁ ⋯ i_{j-1}) = (d_n/a)(d_n/i₁)⋯ ∈ ℤ`.
Convenient formalisation: say `A ∈ ℚ⟦X⟧` is *`d`-integral* if `∀ j, ∃ z : ℤ, d^j * coeff j A = z`
(equivalently `rescale d A ∈ ℤ⟦X⟧`); this is closed under `+`, `*`, integer scalars (Cauchy
product: `d^j ∑_{a+b=j} A_a B_b = ∑ (d^a A_a)(d^b B_b)`), and `C 1 + C (1/i) * X`-type factors
with `i ∣ d` are `d`-integral.

(Alternative route: `F(t) = 4^n (t+1/2)_n / n!` is an integer-valued polynomial of degree `n`;
expand it in the Newton basis `binom(t + k, a)` at `t = -k`; the coefficients are finite
differences of integers.)

**Lean hints.** `Ring.choose`, `descPochhammer`, `ascPochhammer`,
`Polynomial.eval`, `Nat.add_choose_eq` (Vandermonde over `ℕ`), `PowerSeries.coeff_mul`,
`PowerSeries.coeff_prod`, `PowerSeries.rescale`, `PowerSeries.coeff_rescale`,
`Nat.lcmUpto` (`dn n = Nat.lcmUpto n`), `Finset.dvd_lcm` (`i ∈ Icc 1 n → i ∣ lcmUpto n`),
`Nat.centralBinom`, `Nat.succ_mul_centralBinom_succ`, `Finset.prod_range_succ`,
`Finset.prod_range_reflect`.

**Numerical check.** `python/mirror.py`, section "Stmt_BlockF, Stmt_L2a, Stmt_L2b" (`n ≤ 20`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem BlockF_proof : Stmt_BlockF := by
  sorry

end Zeta2

end
