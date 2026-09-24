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

namespace ChainStep

/-! The four fields of `Stmt_ChainStep`, as lemmas (the scout's `Achain_zero`, `Achain_succ`,
`Bchain_zero`, `Bchain_succ`).  `K : Type` (not `Type*`) so that `hS K` applies. -/

variable {K : Type} [Field K]

/-- One pair: `Achain` is one Bailey step applied to `unitα a`. -/
lemma Achain_zero (a : K) (b c : Fin 1 → K) :
    Achain a b c = bα a (b 0) (c 0) (unitα a) := by
  funext r
  simp [Achain, bα]

/-- `m + 2` pairs: split off the last factor of the product (`Fin.prod_univ_castSucc`). -/
lemma Achain_succ (a : K) {m : ℕ} (b c : Fin (m + 2) → K) :
    Achain a b c = bα a (b (Fin.last (m + 1))) (c (Fin.last (m + 1)))
      (Achain a (Fin.init b) (Fin.init c)) := by
  funext r
  simp only [Achain, bα, Fin.prod_univ_castSucc, Fin.init]
  ring

/-- One pair: only the empty chain, and only `j = 0` survives in `bβ … unitβ`. -/
lemma Bchain_zero (a : K) (b c : Fin 1 → K) :
    Bchain a b c = bβ a (b 0) (c 0) unitβ := by
  funext n
  have hch : chains 0 n = {Fin.elim0} := by
    ext i
    simp only [Finset.mem_singleton]
    constructor
    · intro _; funext k; exact k.elim0
    · intro _; rw [mem_chains]; exact ⟨fun k => k.elim0, fun a _ _ => a.elim0⟩
  rw [Bchain, hch, Finset.sum_singleton, bβ, Finset.sum_eq_single 0]
  · simp [bw, unitβ, chainLast, rpoch_zero, Fin.last]
  · intro j _ hj
    simp [unitβ, hj]
  · intro h
    simp at h

/-- `m + 2` pairs: sort the chains by their last entry (`hS`), then the snoc'd chain's factors
are the `Fin.init` chain's factors times the last Bailey weight `bw`. -/
lemma Bchain_succ (hS : Stmt_SumChainsSucc) (a : K) {m : ℕ} (b c : Fin (m + 2) → K) :
    Bchain a b c = bβ a (b (Fin.last (m + 1))) (c (Fin.last (m + 1)))
      (Bchain a (Fin.init b) (Fin.init c)) := by
  funext n
  rw [Bchain, hS K m n _, bβ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Bchain, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [Fin.prod_univ_castSucc, chainLast_snoc]
  have hcast : ∀ k : Fin m, chainFactor a b c (Fin.snoc i' j) k.castSucc =
      chainFactor a (Fin.init b) (Fin.init c) i' k := by
    intro k
    simp only [chainFactor, Fin.snoc_castSucc, chainPrev_snoc_castSucc, Fin.init,
      Fin.succ_castSucc]
  simp only [hcast]
  simp only [chainFactor, bw, Fin.snoc_last, chainPrev_snoc_last, Fin.succ_last, Fin.init]
  ring

end ChainStep

theorem ChainStep_proof (hS : Stmt_SumChainsSucc) : Stmt_ChainStep := by
  exact
    { achain_zero := fun K _ a b c => ChainStep.Achain_zero a b c
      achain_succ := fun K _ a m b c => ChainStep.Achain_succ a b c
      bchain_zero := fun K _ a b c => ChainStep.Bchain_zero a b c
      bchain_succ := fun K _ a m b c => ChainStep.Bchain_succ hS a b c }

end Zeta2.Cited

end
