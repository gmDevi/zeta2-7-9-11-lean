import Zeta2Lean.Statements

/-!
# L2c: `v_p(ρ₀) ≥ -11` for primes `p ≥ 11` with `p² > 2n` (proof.md §4.3 Step 6)

**Task.** Prove `Stmt_L2c` from `Stmt_ResidueForm`, `Stmt_AndrewsApplied`, `Stmt_FJClosed`,
`Stmt_FJKummer`.

**Informal proof.** By ResidueForm and AndrewsApplied,
  `ρ₀ = -24 ∑_{ℓ=1}^{n} ∑_{J ∈ chains 8 (n-ℓ)} [ε^7] F_J(ε)`,
`v_p(24) = 0` (`p ≥ 5`), and `v_p` of a sum is at least the minimum (ultrametric).  So it suffices:
  (★) `v_p([ε^7] F_J) ≥ v_p(F_J(0)) - 7`, and `v_p(F_J(0)) ≥ -4` (FJClosed + FJKummer).
*Derivative lemma (★)* (Zudilin 2004 Lemma 17 style, but without logarithms).  Say a power series
`U` is *`p`-tame* if `v_p([ε^j] U) ≥ -j` for all `j` (`0` counts as `+∞`), i.e. `U(pε)` has
`p`-integral coefficients.  Tame series form a multiplicative monoid (Cauchy product) containing
`1`, and `(1 + βε)^{±1}` is tame whenever `v_p(β) ≥ -1` (coefficients `β^j`, resp. `(-β)^j`).  Now `F_J(ε) = F_J(0) · ∏_s (1 + β_s ε)^{e_s}`, `e_s = ±1`,
over the linear factors of `Fser` (see its definition): each factor is `c + dε` with
`d ∈ {±1, ±2}` and `c ∈ ½ℤ ∖ {0}` whose numerator has absolute value `≤ 2n < p²`:
`ℓ - 2ε`, `ℓ - 1/2 - ε`, `r + 1/2 ∓ ε` (`r < n`), `r + 1 ∓ ε` (`r < n`), `-N + r - ε` (`r < J_i ≤ N`),
`ℓ + 1/2 + r - ε`, `ℓ + 1 + r - ε`, `1/2 - N + r - ε`, `ℓ + 1 + r - 2ε` (all with `r < J_8 ≤ N`, so
`|numerator| ≤ 2n`).  Hence `β = d/c` has `v_p(β) ≥ -1` (`p` odd, `v_p(numerator) ≤ 1`).  So
`F_J / F_J(0)` is tame and `v_p([ε^7] F_J) ≥ v_p(F_J(0)) - 7 ≥ -11`.  (If `F_J(0) = 0` there is
nothing to prove, but it is never `0`.)

**Lean hints.** `padicValRat.min_le_padicValRat_add`, `padicValRat.mul`, `padicValRat.pow`,
`padicValRat.inv`, `padicValRat.neg`, `padicValRat.of_nat`, `padicValNat_le_nat_log`,
`Nat.log_eq_iff`, `PowerSeries.coeff_mul`, `PowerSeries.coeff_prod`, `PowerSeries.constantCoeff_inv`,
`PowerSeries.eq_inv_iff_mul_eq_one`, `Finset.sum_induction` (for "every term ≥ c ⇒ sum ≥ c").
A convenient predicate: `vpGe p c x := x = 0 ∨ c ≤ padicValRat p x` (closed under `+`, and
`vpGe p c x → vpGe p c' y → vpGe p (c+c') (x*y)`).

**Numerical check.** `python/mirror.py`, section "... Stmt_L2c ..." (`n ≤ 60`, all such `p`);
proof.md §9 `perell_check.py`: per-`ℓ` bound attained.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem L2c_proof (hR : Stmt_ResidueForm) (hA : Stmt_AndrewsApplied) (hC : Stmt_FJClosed)
    (hK : Stmt_FJKummer) : Stmt_L2c := by
  sorry

end Zeta2

end
