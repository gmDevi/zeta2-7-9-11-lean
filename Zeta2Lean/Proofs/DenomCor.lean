import Zeta2Lean.Statements

/-!
# L2 corollary: `D_n = d_n^{12}/Φ_n` clears all denominators (proof.md §4.4; LSZ Lemma 5.4)

**Task.** Prove `Stmt_L2cor` from `Stmt_L2a`, `Stmt_L2b`, `Stmt_L2c`:
`D_n ρ₀, D_n Z₇, D_n Z₉, D_n Z₁₁ ∈ ℤ`.

**Informal proof.** `Φ_n ∣ d_n` (`Phi_dvd_dn` in `Defs.lean`) and `D_n Φ_n = d_n^{12}`
(`Dn_mul_Phi`).
* `Z`'s: by L2a, `d_n^{8-i} c_i = ∑_k d_n^{8-i} r_{i,k} ∈ ℤ`.  `D_n = d_n^{8-i} · (d_n^{4+i}/Φ_n)` and
  `Φ_n ∣ d_n ∣ d_n^{4+i}`, so `D_n c_i ∈ ℤ` for `i = 3, 5, 7`; multiply by `46080`, `860160`,
  `10321920`.
* `ρ₀`: show `v_q(D_n ρ₀) ≥ 0` for every prime `q` (or `ρ₀ = 0`).  If `q ∣ Φ_n`, i.e.
  `q ≤ n`, `q ≥ 11`, `q² > 2n`: then `v_q(d_n) = ⌊log_q n⌋ = 1` (`q ≤ n < q²`), `v_q(Φ_n) = 1`, so
  `v_q(D_n) = 12 - 1 = 11`, and `v_q(ρ₀) ≥ -11` (L2c).  Otherwise `v_q(D_n) = 12 v_q(d_n)` and
  `v_q(d_n^{12} ρ₀) ≥ 0` (L2b).  A rational with non-negative valuation at every prime is an integer.

**Lean hints.** `Phi_dvd_dn`, `Dn_mul_Phi`, `Dn_pos` (in `Defs.lean`); `Nat.factorization_lcmUpto`,
`Nat.log_eq_iff`, `Nat.factorization_prod`, `Nat.Prime.factorization_self`, `Nat.padicValNat_def`,
`padicValRat.mul`, `padicValRat_of_nat`, `Nat.factorization_def`, `Rat.den_eq_one_iff`,
`Nat.eq_one_iff_not_exists_prime_dvd`, `padicValRat.of_int`, `Int.cast_sum`, `Finset.mul_sum`,
`Nat.cast_div` (`Φ_n ∣ d_n^{12}`, `Phi_pos`).

**Numerical check.** `python/mirror.py`, section "... Stmt_L2cor" (`n ≤ 60`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem L2cor_proof (h2a : Stmt_L2a) (h2b : Stmt_L2b) (h2c : Stmt_L2c) : Stmt_L2cor := by
  sorry

end Zeta2

end
