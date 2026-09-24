import Zeta2Lean.Statements

/-!
# Translation formula for `(t + 1/2)^{-s}` (proof.md P1; LSZ Lemma 2.4; Robert §5.3)

**Task.** Prove `Stmt_Translation`:
`HasVolkenborn (halfPow s) I → HasVolkenborn (fun x => halfPow s (x + k)) (I - s ∑_{ℓ<k} halfPow (s+1) ℓ)`.
No hypotheses (the convergence of the unshifted sums is an assumption of the statement).

**Informal proof.** Let `f = halfPow s`.  For every `N`,
  `∑_{x<2^N} f(x+k) = ∑_{x<2^N} f(x) + ∑_{ℓ<k} (f(ℓ + 2^N) - f(ℓ))`
(induction on `k`, or `Finset.sum_range_add_sum_Ico` twice), hence
  `volkenbornSum (f(·+k)) N = volkenbornSum f N + ∑_{ℓ<k} (f(ℓ + 2^N) - f(ℓ)) / 2^N`.
For fixed `ℓ`, with `u = ℓ + 1/2` (`‖u‖ = 2`, `u⁻¹ = 2/(2ℓ+1)`) and `h = 2^N` (`‖h‖ = 2^{-N} → 0`):
  `((u+h)^{-s} - u^{-s}) / h + s u^{-s-1} = h · E(ℓ, N)`  with `‖E(ℓ,N)‖ ≤ C_{s}`
(algebra: `(u+h)^{-s} - u^{-s} + s h u^{-s-1} = h² Q(u,h) / (u^{s+1}(u+h)^s)`, `Q ∈ ℤ[u,h]`; in
terms of `u' = 2ℓ+1`, `h' = 2^{N+1}` everything is a 2-adic unit or integer).  So each summand
tends to `-s · halfPow (s+1) ℓ`; add the finitely many limits (`tendsto_finsetSum`) to the
hypothesis `volkenbornSum f N → I` (`Filter.Tendsto.add`).

**Lean hints.** `Finset.sum_range_add_sum_Ico`, `Finset.sum_range_succ`, `Finset.sum_sub_distrib`,
`Filter.Tendsto.add`, `Filter.Tendsto.sub`, `tendsto_finsetSum`, `tendsto_pow_atTop_nhds_zero_of_lt_one`
(for `2^{-N} → 0` in `ℝ`), `Padic.norm_p_pow`, `Padic.nonarchimedean`, `Padic.norm_int_le_one`,
`squeeze_zero_norm` / `tendsto_iff_norm_sub_tendsto_zero` (for `‖a_N - L‖ ≤ C 2^{-N} → 0`),
`volkenbornSum_add` and `HasVolkenborn.add`, `HasVolkenborn.sum` (in `Defs.lean`).
Writing `halfPow s x = 2^s * ((2*x+1 : ℕ) : ℚ_[2])⁻¹ ^ s` first is convenient.

**Numerical check.** `python/mirror.py`, section "J_s ...": `v₂(R_12 - (J_s - s A_k)) ≥ 20`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem Translation_proof : Stmt_Translation := by
  sorry

end Zeta2

end
