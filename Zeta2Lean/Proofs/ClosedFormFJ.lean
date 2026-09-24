import Zeta2Lean.Statements

/-!
# Closed form of `F_J(0)` (proof.md §4.3 Step 4)

**Task.** Prove `Stmt_FJClosed : constantCoeff (Fser n ℓ J) = FJ0 n ℓ J` for `1 ≤ ℓ ≤ n`,
`J ∈ chains 8 (n-ℓ)`.  No hypotheses.

**Informal proof.** `constantCoeff` is a ring hom, `constantCoeff (φ⁻¹) = (constantCoeff φ)⁻¹`,
`constantCoeff (psPoch c d k) = rpoch c k`.  So `F_J(0)` is the product of the constant terms:
  `F_J(0) = -(N+1) ℓ P_ℓ(0) ∏_{i=1}^{8} (1/2)_{d_i}/d_i! ∏_{i=1}^{7} (-N)_{J_i}(ℓ+1/2)_{J_i}/((ℓ+1)_{J_i}(1/2-N)_{J_i})
          · (ℓ+1)_{J_8} (-N)_{J_8} / ((J_8+1)(ℓ+1)_{J_8}(1/2-N)_{J_8})`,
  `P_ℓ(0) = 2^{16n} (ℓ-1/2)^3 (1/2)_{ℓ-1}^8 (1/2)_N^8 / (ℓ!^8 N!^8)`.
Use (all for natural numbers, `J ≤ N`):
* `(1/2)_m / m! = C(2m,m) / 4^m`;  `(1/2)_{ℓ-1}/ℓ! = C(2ℓ-2,ℓ-1) / (4^{ℓ-1} ℓ)`;
* `(-N)_J (ℓ+1/2)_J / ((ℓ+1)_J (1/2-N)_J) = C(2(ℓ+J),ℓ+J) C(2(N-J),N-J) / (C(2ℓ,ℓ) C(2N,N))`;
* `(-N)_J / ((J+1)(1/2-N)_J) = 4^J C(2(N-J),N-J) / ((J+1) C(2N,N))`  (and `(ℓ+1)_{J_8}` cancels).
Then all powers of 2 collapse (`∑ d_i = J_8`, `2^{16n} = 4^{8ℓ} 4^{8N}`) and one obtains
  `F_J(0) = -64 (2ℓ-1)^{-4} C(2ℓ-2,ℓ-1) (N+1)/(J_8+1) ∏_{i≤8} C(2d_i,d_i)
           ∏_{i≤7} C(2(ℓ+J_i),ℓ+J_i) ∏_{i≤8} C(2(N-J_i),N-J_i)`  (= `FJ0`).
Sanity check of the constants: `ℓ P_ℓ(0)` contributes `2^{16n} (ℓ-1/2)^3 ((1/2)_{ℓ-1}/ℓ!)^8 ℓ^8/ℓ^7 …`;
the numerical mirror confirms the identity exactly for `n ≤ 5`.

**Lean hints.** `map_prod`, `map_mul`, `map_pow`, `PowerSeries.constantCoeff_inv`,
`PowerSeries.constantCoeff_C`, `PowerSeries.constantCoeff_X`, `Finset.prod_range_succ`,
`Nat.centralBinom`, `Nat.succ_mul_centralBinom_succ`, `Nat.cast_choose`,
`Nat.choose_mul_factorial_mul_factorial`, `Fin.prod_univ_castSucc`, `Fin.prod_univ_eight`,
`field_simp`, `ring`.  Useful: prove `rpoch (1/2 : ℚ) m = (2m)! / (4^m m!)` by induction; then
express `rpoch (-N) J = (-1)^J N!/(N-J)!`, `rpoch (1/2 - N) J = (-1)^J (1/2)_N / (1/2)_{N-J}`, etc.
Membership `J ∈ chains 8 (n-ℓ)` gives monotonicity and `J i ≤ n - ℓ` (so `n - ℓ - J i` is honest):
`mem_chains`, `chainPrev_le` (proved in `Defs.lean`).

**Numerical check.** `python/mirror.py`, section "... Stmt_FJClosed ..." (all chains, `n ≤ 5`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

theorem FJClosed_proof : Stmt_FJClosed := by
  sorry

end Zeta2

end
