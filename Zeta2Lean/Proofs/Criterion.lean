import Zeta2Lean.Statements

/-!
# Lai's irrationality criterion (proof.md P4; Lai arXiv:2304.00816, Lemma 2.1)

**Task.** Prove `Stmt_Criterion`: if `|a_{m,j}| ≤ B_m` (all `j`, including `j = 0`), the forms
`L_m = a_{m,0} + ∑_j a_{m,j} α_j ∈ ℚ_[2]` are frequently non-zero, and `B_m ‖L_m‖ → 0`, then not all
`α_j` are rational.  No hypotheses.

**Informal proof.** Suppose `α_j = q_j ∈ ℚ` for all `j`.  Let `D ≥ 1` be a common denominator
(e.g. `D = ∏_j (q_j).den`), so `D q_j ∈ ℤ`.  Then `D L_m = D a_{m,0} + ∑_j a_{m,j} (D q_j)` is an
integer `z_m`, with `|z_m| ≤ B_m · E`, `E := D + ∑_j |D q_j|`.  For the (frequent) `m` with
`L_m ≠ 0`: `z_m ≠ 0`, and for a non-zero integer `‖(z : ℚ_[2])‖ ≥ 1/|z|` (since `2^{v₂(z)} ∣ z`,
`2^{v₂(z)} ≤ |z|`).  Hence `B_m ‖L_m‖ = B_m ‖z_m‖ / ‖D‖ ≥ B_m / (|z_m| ‖D‖) ≥ 1/(E ‖D‖) > 0`
(note `B_m > 0` there, because `1 ≤ |z_m| ≤ B_m E`).  This contradicts `B_m ‖L_m‖ → 0`
(take `ε = 1/(E‖D‖)`: eventually `< ε`, but frequently `≥ ε`).

**Lean hints.** `Rat.num_div_den`, `Rat.den_nz`, `Finset.prod_ne_zero_iff`, `Padic.norm_int_le_one`,
`Padic.norm_eq_zpow_neg_valuation`, `padicValInt`, `Int.natAbs`, `padicValNat_dvd_iff_le` /
`pow_padicValNat_dvd`, `Nat.le_of_dvd`, `Filter.Frequently.and_eventually`,
`Filter.Tendsto.eventually_lt_const` (or `(tendsto_order.1 h).2`), `Filter.Frequently.exists`.
Casting: `(((z : ℤ) : ℚ) : ℚ_[2]) = (z : ℚ_[2])` via `push_cast`; `Rat.cast_intCast`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem Criterion_proof : Stmt_Criterion := by
  sorry

end Zeta2

end
