import Zeta2Lean.Statements

/-!
# Convergence of the Riemann sums of `(x + 1/2)^{-s}` (proof.md P1, P2)

**Task.** Prove `Stmt_JConv : ∀ s, HasVolkenborn (halfPow s) (J s)`.  No hypotheses.

**Informal proof.** Since `J s = limUnder atTop (volkenbornSum (halfPow s))`, it suffices to show
that `R_N := volkenbornSum (halfPow s) N` is a Cauchy sequence in the complete space `ℚ_[2]`;
then `cauchySeq_tendsto_of_complete` gives a limit and `tendsto_nhds_limUnder` identifies it with
`J s`.  For `s = 0` the sums are constantly `1`.

Write `halfPow s x = 2^s (2x+1)^{-s}` (`(x + 1/2)⁻¹ = 2 (2x+1)⁻¹`).  Then
  `R_{N+1} - R_N = 2^{-N-1} ∑_{x<2^N} (f(x + 2^N) - f(x))`,  `f = halfPow s`
(split `range (2^{N+1}) = range (2^N) ∪ [2^N, 2^{N+1})`).  With `u = 2x+1` (odd) and `H = 2^{N+1}`:
  `(u+H)^{-s} - u^{-s} + s H u^{-s-1} = H² · Q(u,H) / (u^{s+1} (u+H)^s)`,  `Q ∈ ℤ[u,H]`
(clear denominators: `u^{s+1} - (u+H)^s u + s H (u+H)^s` is divisible by `H²` as a polynomial in
`H`), so this error term has norm `≤ ‖H‖² = 2^{-2N-2}` (`u`, `u+H` are odd, i.e. 2-adic units).
The main term is `-s H ∑_{u odd < 2^{N+1}} u^{-(s+1)}`.  **Odd power sums**: for `k ≥ 1`,
`S_M(k) := ∑_{u odd, u < 2^M} u^{-k}` has `v₂(S_M(k)) ≥ M - 1`.  Proof by pairing `u ↔ 2^M - u`
(`Finset.sum_range_reflect` on `x ↦ 2x+1`): `(2^M - u)^{-k} ≡ (-u)^{-k} (mod 2^M)`; for odd `k`
the pairs cancel mod `2^M`; for even `k` they double, giving `S_M ≡ 2 S_{M-1} (mod 2^M)` and the
bound by induction (`S_1 = 1`).  [Alternative: `u ↦ 3u` permutes odd residues mod `2^M`, so
`(3^{-k} - 1) S_M ≡ 0 (mod 2^M)`, and `v₂(3^k - 1) ≤ 2k`; any bound `v₂(S_M) ≥ M - c(k)` suffices.]
Hence `‖R_{N+1} - R_N‖ ≤ 2^{N+1} · 2^{-s} · max(2^{-(N+1)} 2^{-N}, 2^{-2N-2}) ≤ C_s · 2^{-N}`, and
`cauchySeq_of_le_geometric` (with `r = 1/2`) applies (`dist = ‖· - ·‖`).

**Lean hints (names verified in this Mathlib).**
* `cauchySeq_of_le_geometric (r C : ℝ) (hr : r < 1) (hu : ∀ n, dist (f n) (f (n+1)) ≤ C * r^n)`,
  `cauchySeq_tendsto_of_complete`, `tendsto_nhds_limUnder` (`Filter.limUnder`),
  `HasVolkenborn.volkenborn_eq` (in `Defs.lean`).
* Norms: `Padic.norm_p_pow : ‖(p:ℚ_[p])^n‖ = p^(-n)`, `Padic.norm_p_zpow`, `Padic.norm_int_le_one`,
  `Padic.norm_natCast_eq_one_iff : ‖(n:ℚ_[p])‖ = 1 ↔ p.Coprime n`, `Padic.nonarchimedean`,
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Padic.norm_le_pow_iff_norm_lt_pow_add_one`.
* Sums: `Finset.sum_range_add_sum_Ico`, `Finset.sum_range_reflect`, `Finset.range_eq_Ico`,
  `pow_succ`, `Finset.sum_range_succ`.
* It may be convenient to prove everything for `g x := ((2*x+1 : ℕ) : ℚ_[2])⁻¹ ^ s` and use
  `halfPow s x = 2^s * g x` together with `volkenbornSum_const_mul` (in `Defs.lean`).

**Numerical check.** `python/mirror.py`, section "J_s: cache ... vs Riemann sums":
`v₂(R_N - J_s) ≈ N + const` for `s = 6, 8, 10`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem JConv_proof : Stmt_JConv := by
  sorry

end Zeta2

end
