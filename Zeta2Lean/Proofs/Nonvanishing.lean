import Zeta2Lean.Statements

/-!
# L5: `v₂(S_n) = 32n + 14 - 11m` along `n = 2^m - 1` (proof.md §7)

**Task.** Prove `Stmt_L5` from `Stmt_Delta`, `Stmt_Leibniz`, `Stmt_LeibTermBound`, `Stmt_L5Dom`:
for `m ≥ 2` and any `I` with `HasVolkenborn (integrand (2^m-1)) I`, `‖I‖ = 2^{-target m}`.

**Informal proof.** Let `n = 2^m - 1`, `k₀ = 2^{m-1}`, `t = target m`.
1. *Split off the dominant term.*  By `Stmt_Leibniz`,
   `integrand n x = domTerm m x + rest x`, `rest x := ∑_{(γ,β,M) ≠ (1,0,2·[k₀])} leibTerm n γ β M x`,
   using that `(1, 0, Finsupp.single k₀ 2)` is one of the indices (`k₀ ∈ Icc 1 n`) and
   `leibTerm n 1 0 (Finsupp.single k₀ 2) x = domTerm m x` (unfold: `∏_l C(8, M l) = C(8,2) = 28`,
   `-6 · 2 · 28 = -336`, exponent `5+1+0 = 6`, `∏_l (W_l Y_l)^{M l} = (W_{k₀} Y_{k₀})^2`).
2. *Combinatorics.*  For every other index, `βm + ∑_l v₂C(8, M l) + ∑_{l≠k₀} M l ≥ 3`:
   `v₂C(8,j) = 0, 3, 2, 3` for `j = 0, 1, 2, 3` and `M l ≤ 3`.  If some `M l ∈ {1, 3}`, the middle
   sum is `≥ 3`.  Otherwise every `M l ∈ {0, 2}`, so `a = ∑ M l ∈ {0, 2}`: `a = 0` forces
   `β = 3 - γ ≥ 2`, `βm ≥ 4`; `a = 2` means `M = single l 2`: if `l ≠ k₀` the sum is `2 + 2`; if
   `l = k₀` then `β ≥ 1` (else it is the dominant index), `βm + 2 ≥ 4`.
   Hence by `Stmt_LeibTermBound` (and `Delta.monoAll`) every other term has `Δ ≥ t + 2`, and
   `Δ(rest) ≥ t + 2` (`Delta.sumAll`), so `‖volkenbornSum rest M‖ ≤ 2^{-(t+1)}` for all `M`
   (`Delta.riemannAll`).
3. *Dominant term.*  By `Stmt_L5Dom` and `Delta.riemann`, for `M ≥ m`:
   `‖volkenbornSum dom M - volkenbornSum dom m‖ ≤ 2^{-(t+1)}` and `‖volkenbornSum dom m‖ = 2^{-t}`.
4. Hence for `M ≥ m`, `volkenbornSum integrand M = volkenbornSum dom m + (small)` with
   `‖small‖ ≤ 2^{-(t+1)} < 2^{-t}`, so `‖volkenbornSum integrand M‖ = 2^{-t}`
   (`volkenbornSum_add` in `Defs.lean`, `Padic.norm_eq_of_norm_add_lt_right`).
5. The norm is continuous and eventually constant along the convergent sequence, so `‖I‖ = 2^{-t}`
   (`Filter.Tendsto.norm`, `tendsto_nhds_unique`, `tendsto_const_nhds`, `Filter.EventuallyEq`).

**Lean hints.** `volkenbornSum_add`, `volkenbornSum_sum` (in `Defs.lean`), `Finset.sum_erase_add`,
`Finset.add_sum_erase`, `Finset.sum_sigma'` (flatten the triple sum into a `Finset (Σ …)` or use
nested `Finset.sum_congr`), `Finsupp.single_apply`, `Finset.mem_finsuppAntidiag`,
`Finsupp.support_single`, `Filter.Tendsto.norm`, `tendsto_nhds_unique`,
`Filter.Tendsto.congr'`, `Filter.eventually_ge_atTop`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.
`padicValNat 2 (Nat.choose 8 j)` for `j ≤ 3` by `decide`/`norm_num` (`C(8,1)=8`, `C(8,2)=28`,
`C(8,3)=56`).

**Numerical check.** `python/mirror.py`, section "Stmt_L5": exact `v₂(S_n) = target m` for
`m = 2..7` via the 17000-bit `J`-values; section "Stmt_LeibTermBound" checks `domTerm = leibTerm`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

theorem L5_proof (hD : Stmt_Delta) (hL : Stmt_Leibniz) (hB : Stmt_LeibTermBound)
    (hDom : Stmt_L5Dom) : Stmt_L5 := by
  sorry

end Zeta2

end
