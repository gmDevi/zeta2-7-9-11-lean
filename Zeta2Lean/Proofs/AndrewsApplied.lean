import Zeta2Lean.Statements

/-!
# Andrews' transformation applied to `T_{n,ℓ}` (proof.md §4.3 Steps 2–3; LSZ Lemma 5.3)

**Task.** Prove `Stmt_AndrewsApplied` from the cited `Andrews_Stmt`:
for `1 ≤ ℓ ≤ n`, `Tser n ℓ = ∑_{J ∈ chains 8 (n-ℓ)} Fser n ℓ J` in `PowerSeries ℚ`.

**Informal proof.** Put `N := n - ℓ`, `k = ℓ + κ` (`0 ≤ κ ≤ N`), and (in a field containing
`ℚ⟦ε⟧`, see below) `a := -n + 2ℓ - 2ε`, `b := -N - ε`, `c := ℓ + 1/2 - ε`, so
`1+a-b = ℓ+1-ε`, `1+a-c = 1/2-N-ε`, `1+a-b-c = 1/2`, `1+a+N = ℓ+1-2ε`, `a+N = ℓ-2ε`,
`n-2k+2ε = -(a+2κ)`.
*Step 2 (VWP form).* Using `(x)_{N-κ} = (-1)^κ (x)_N / (1-x-N)_κ` for `x = 1/2+ε` and `x = 1+ε`, and
`(1-ε)_{ℓ+κ} = (1-ε)_ℓ (ℓ+1-ε)_κ`, `(ℓ+1/2-ε)_{k-ℓ} = (c)_κ`:
  `T_{n,ℓ} = -a · P_ℓ · ∑_{κ=0}^{N} (a+2κ)/a · [(b)_κ (c)_κ / ((1+a-b)_κ (1+a-c)_κ)]^8`
(`P_ℓ = Pser n ℓ`).
*Step 3 (Andrews).* Apply `Andrews_Stmt` with `m = 8`, `(b_k, c_k) = (b, c)` for `k < 8` and
`(b_8, c_8) = (1, 1 + a + N)` (this is the `δ = 0` value of proof.md's `c₉ = ℓ+1-2ε-δ`; at `δ = 0`
all denominators are non-zero, so no limit is needed).  Left side, term `κ ≤ N`: the pair `(1, 1+a+N)`
contributes `κ! (1+a+N)_κ / ((a)_κ (-N)_κ)`, which cancels `(a)_κ/κ!` and `(-N)_κ/(1+a+N)_κ`, leaving
`(a+2κ)/a · [...]^8`.  Right side: the prefactor is
`(1+a)_N (-1-N)_N / ((a)_N (-N)_N) = (N+1)(a+N)/a`; `b_8 + c_8 - a - N = 2`, `(2)_J = (J+1)!`;
the `k = 8` factor is `(1/2)_{d_8}/d_8! · J_8! (ℓ+1-2ε)_{J_8} / ((ℓ+1-ε)_{J_8} (1/2-N-ε)_{J_8})`.
Multiplying by `-a P_ℓ` gives exactly `∑_J F_J` (see the docstring of `Fser`).
Hypotheses of `Andrews_Stmt`: `a ≠ 0`, `(ℓ+1-ε)_N ≠ 0`, `(1/2-N-ε)_N ≠ 0`, `(a)_N ≠ 0`,
`(-N)_N = (-1)^N N! ≠ 0`, `(ℓ+1-2ε)_N ≠ 0`, `(2)_N ≠ 0` — each factor has non-zero `ε`-coefficient
or is a non-zero rational.
*Choice of field.* `K := FractionRing (PowerSeries ℚ)` (a field of characteristic 0, `ℚ⟦X⟧` is a
domain) or `K := LaurentSeries ℚ` (Mathlib has `Field (LaurentSeries ℚ)`, and
`HahnSeries.ofPowerSeries ℤ ℚ` is an injective ring hom).  Push the definitions of `Tser`, `Fser`
through the injective ring hom `φ : ℚ⟦X⟧ → K`; for units, `φ (u⁻¹) = (φ u)⁻¹`
(from `u * u⁻¹ = 1`); `φ (psPoch c d k) = rpoch (φ (C c + C d X)) k` after reindexing
(`psPoch c d k = ∏_{j<k} ((C c + C d X) + j)`).

**Lean hints.** `IsFractionRing.injective`, `algebraMap`, `map_prod`, `map_pow`, `map_mul`,
`PowerSeries.mul_inv_cancel`, `PowerSeries.constantCoeff_inv`, `eq_inv_of_mul_eq_one_left`,
`Finset.prod_range_reflect`, `Finset.prod_range_add`, `Finset.sum_bij`, `Finset.sum_nbij'`,
`Fin.prod_univ_castSucc`, `Fin.prod_univ_succ`, `Fin.last`, `div_eq_mul_inv`, `field_simp`.
Suggested lemmas to prove first (in `K`): reflection `rpoch x (N - κ) = (-1)^κ rpoch x N / rpoch (1-x-N) κ`
(`κ ≤ N`, denominators ≠ 0); `rpoch x (a + b) = rpoch x a * rpoch (x + a) b`;
`rpoch (-N) N = (-1)^N N!`; `rpoch (1+a) N / rpoch a N = (a+N)/a`; `rpoch (-1-N) N / rpoch (-N) N = N+1`.

**Numerical check.** `python/mirror.py`, section "Stmt_ResidueForm, Stmt_AndrewsApplied, ..."
(identity of truncated power series, `n ≤ 5`, all `ℓ`), and "Andrews_Stmt ... specialisation".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem AndrewsApplied_proof (hA : Andrews_Stmt) : Stmt_AndrewsApplied := by
  sorry

end Zeta2

end
