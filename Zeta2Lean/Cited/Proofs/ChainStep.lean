import Zeta2Lean.Cited.Statements

/-!
# The chain pair is the iterated Bailey pair (Andrews track)

**Task.** Prove `Stmt_ChainStep` (four fields) from `Stmt_SumChainsSucc` (hypothesis `hS`), in
every field `K` (Lean's `x / 0 = 0` included; no characteristic or non-vanishing assumption):
* `achain_zero`: `Achain a b c = bα a (b 0) (c 0) (unitα a)` for `b c : Fin 1 → K`;
* `achain_succ`: `Achain a b c = bα a (b L) (c L) (Achain a (Fin.init b) (Fin.init c))`,
  `L = Fin.last (m+1)`, for `b c : Fin (m + 2) → K`;
* `bchain_zero`: `Bchain a b c = bβ a (b 0) (c 0) unitβ`;
* `bchain_succ`: `Bchain a b c = bβ a (b L) (c L) (Bchain a (Fin.init b) (Fin.init c))`.

**Informal proof.**
* `Achain`: the product over `Fin (m+2)` splits off the last factor (`Fin.prod_univ_castSucc`),
  and `Fin.init b k = b k.castSucc`; for `m + 1 = 1` the product has one factor.  `ring`.
* `bchain_zero`: `chains 0 n = {Fin.elim0}` (the empty chain), the empty product is `1`,
  `chainLast = 0`; on the right only `j = 0` survives in `bβ` (`unitβ j = [j = 0]`,
  `Finset.sum_eq_single`), and `bw a ρ σ n 0` is the same expression.
* `bchain_succ`: expand `Bchain` (chains of length `m + 1` in `[0, n]`) with `hS` into
  `∑_{j ≤ n} ∑_{i' ∈ chains m j}` of the summand at `Fin.snoc i' j`; for the snoc'd chain,
  `chainFactor` at `k.castSucc` equals `chainFactor` of `(init b, init c, i')` at `k`
  (`Fin.snoc_castSucc`, `chainPrev_snoc_castSucc`, `Fin.succ_castSucc`), the last factor uses
  `chainPrev_snoc_last`, `chainLast_snoc` (proved in `Cited/Defs.lean`) and `Fin.succ_last`,
  and together with the tail factor it is exactly `bw a (b L) (c L) n j`; `Finset.mul_sum`, `ring`.

**Lean route (complete, compiled).** `docs/cited/AndrewsScout.lean`, lines 598–646
(`Achain_zero`, `Achain_succ`, `Bchain_zero`, `Bchain_succ`; there `Bchain_succ` rewrites with
`sum_chains_succ`, here use `hS K m n _` instead).  The structure instance
`{ achain_zero := fun K _ a b c => Achain_zero a b c, … }` was checked to typecheck against
`Stmt_ChainStep`.  All definitions (`Achain`, `Bchain`, `chainFactor`, `bα`, `bβ`, `bw`,
`unitα`, `unitβ`) and the `Fin.snoc` chain API are in `Cited/Defs.lean` with the same names and
bodies.  Put helpers in `namespace Zeta2.Cited.ChainStep` (or make them `private`); only
`Zeta2.Cited.ChainStep_proof` is exported.

**Numerical check.** `python3 python/cited_mirror.py`, section `Stmt_ChainStep` (random rational
parameters including vanishing denominators, evaluated with `x / 0 = 0`).
-/

open Finset

noncomputable section

namespace Zeta2.Cited

theorem ChainStep_proof (hS : Stmt_SumChainsSucc) : Stmt_ChainStep := by
  sorry

end Zeta2.Cited

end
