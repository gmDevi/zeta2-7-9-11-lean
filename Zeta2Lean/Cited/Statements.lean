import Zeta2Lean.Cited.Defs

/-!
# Zeta2Lean.Cited.Statements — one `Prop` per sub-lemma of the two cited hypotheses

Same pattern as `Zeta2Lean/Statements.lean`: every sub-lemma is a `def Stmt_X : Prop` (or a
`structure` with named fields); `Cited/Proofs/*.lean` prove them, taking the statements they depend
on as hypotheses; `Cited/Assembly.lean` derives the two cited hypotheses of the main theorem,
`PNT_Stmt` and `Andrews_Stmt`, from them; `Cited/Main.lean` wires everything together.

Every statement below is true: the Andrews-track statements are exactly the lemmas of the Andrews
scout's complete, compiled proof (`docs/cited/AndrewsScout.lean`), and `Stmt_WienerIkehara` is the
theorem `WienerIkehara.tendsto_sum_div` of mathlib4 PR #43238 with its hypothesis class unbundled.
All statements are checked numerically (exact arithmetic, Lean's `x / 0 = 0` semantics) by
`python/cited_mirror.py`.

## PNT track (route: vendor the Wiener–Ikehara theorem from mathlib4 PRs #43046/#43233/#43238)

`PNT_Stmt ⇐ Stmt_WienerIkehara` (`Cited/Assembly.lean`, `pnt_of_stmts`): apply Wiener–Ikehara to
`f = Λ` (the residue class `0 mod 1`), `A = 1`, `C = log 4 + 4` (Chebyshev), and
`G = LFunctionResidueClassAux (0 : ZMod 1) = -ζ'/ζ - 1/(s-1)` (continuous on `re s ≥ 1` by the
non-vanishing of `ζ` on `re s = 1`; all in Mathlib, `NumberTheory/LSeries/PrimesInAP.lean`).

## Andrews track (route: the `q = 1` Bailey chain; no Whipple, no Dougall)

```
Andrews_Stmt ⇐ Stmt_BPChain ⇐ Stmt_UnitPair, Stmt_BaileyLemma (⇐ Stmt_PPS),
                               Stmt_ChainStep (⇐ Stmt_SumChainsSucc)
```
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Cited

/-! ## PNT track -/

/-- **Wiener–Ikehara Tauberian theorem** (mathlib4 PR #43233/#43238,
`WienerIkehara.tendsto_sum_div`, adapted from PrimeNumberTheoremAnd; the fields of the class
`WienerIkehara` in the same order: `f, C, bound, A, hA, G, hG, hG', hf, hpos`).
Let `f : ℕ → ℝ` be non-negative with the Chebyshev-type bound `∑_{i<n} |f i| ≤ C n`, whose
`L`-series converges for real `σ > 1` and, after subtracting `A/(s-1)`, extends continuously
(as `G`) to the closed half-plane `re s ≥ 1`.  Then `(∑_{n ≤ x} f n) / x → A`.
(`LSeries` ignores `f 0`; the sum includes it, which does not change the limit.) -/
def Stmt_WienerIkehara : Prop :=
  ∀ (f : ℕ → ℝ) (C A : ℝ) (G : ℂ → ℂ),
    (∀ n : ℕ, ∑ i ∈ range n, |f i| ≤ C * n) →
    0 ≤ A →
    ContinuousOn G {s | 1 ≤ s.re} →
    Set.EqOn G (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - (A : ℂ) / (s - 1)) {s | 1 < s.re} →
    (∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n ↦ (f n : ℂ)) σ) →
    0 ≤ f →
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A)

/-! ## Andrews track -/

/-- **Polynomial Pfaff–Saalschütz**, in every field (no characteristic assumption):
`∑_{s=0}^{M} C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} = (z-x)_M (z-y)_M (z+M)_M`.
(Dividing by `M!` and `(z)_{2M}` gives the terminating Pfaff–Saalschütz sum
`₃F₂(-M, x, y; z, 1+x+y-z-M; 1) = (z-x)_M (z-y)_M / ((z)_M (z-x-y)_M)`; the polynomial form has
no denominators, so it holds for all `x, y, z`, in particular at the non-positive integers
`z = 1+a+2r` that `Andrews_Stmt` allows.) -/
def Stmt_PPS : Prop :=
  ∀ (K : Type) [Field K] (x y z : K) (M : ℕ),
    ∑ s ∈ range (M + 1), (M.choose s : K) * rpoch x s * rpoch y s * rpoch (z - x - y) (M - s) *
        rpoch (z + s) (2 * M - s) =
      rpoch (z - x) M * rpoch (z - y) M * rpoch (z + M) M

/-- **The unit Bailey pair**: `α_r = (a+2r)/a (a)_r (-1)^r / r!`, `β_n = [n = 0]` is a Bailey
pair relative to `a` at every level, for `a ≠ 0` (characteristic zero). -/
def Stmt_UnitPair : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (a : K), a ≠ 0 → ∀ n : ℕ, BP a (unitα a) unitβ n

/-- **Bailey's lemma** (`q = 1`, polynomial normalisation): if `(α, β)` is a Bailey pair relative
to `a` at all levels `j ≤ n`, and `(1+a-ρ)_n, (1+a-σ)_n ≠ 0`, then so is
`(bα a ρ σ α, bβ a ρ σ β)` at level `n`. -/
def Stmt_BaileyLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (a ρ σ : K) (α β : ℕ → K) (n : ℕ),
    rpoch (1 + a - ρ) n ≠ 0 → rpoch (1 + a - σ) n ≠ 0 → (∀ j ≤ n, BP a α β j) →
    BP a (bα a ρ σ α) (bβ a ρ σ β) n

/-- **Chains sorted by their last entry**: a chain `0 ≤ i₁ ≤ ⋯ ≤ i_{m+1} ≤ n` is a chain
`0 ≤ i₁ ≤ ⋯ ≤ i_m ≤ j` followed by `j = i_{m+1} ≤ n` (`Fin.snoc` / `Fin.init`). -/
def Stmt_SumChainsSucc : Prop :=
  ∀ (M : Type) [AddCommMonoid M] (m n : ℕ) (f : (Fin (m + 1) → ℕ) → M),
    ∑ i ∈ chains (m + 1) n, f i = ∑ j ∈ range (n + 1), ∑ i' ∈ chains m j, f (Fin.snoc i' j)

/-- **The chain pair is the iterated Bailey pair**: `(Achain, Bchain)` for `m + 1` pairs is one
Bailey step, with the last pair `(b (last), c (last))`, applied to `(Achain, Bchain)` for the
first `m` pairs (`Fin.init`), and for one pair it is one Bailey step applied to the unit pair.
These are identities in every field (Lean's `x / 0 = 0` included). -/
structure Stmt_ChainStep : Prop where
  achain_zero : ∀ (K : Type) [Field K] (a : K) (b c : Fin 1 → K),
    Achain a b c = bα a (b 0) (c 0) (unitα a)
  achain_succ : ∀ (K : Type) [Field K] (a : K) (m : ℕ) (b c : Fin (m + 2) → K),
    Achain a b c =
      bα a (b (Fin.last (m + 1))) (c (Fin.last (m + 1))) (Achain a (Fin.init b) (Fin.init c))
  bchain_zero : ∀ (K : Type) [Field K] (a : K) (b c : Fin 1 → K),
    Bchain a b c = bβ a (b 0) (c 0) unitβ
  bchain_succ : ∀ (K : Type) [Field K] (a : K) (m : ℕ) (b c : Fin (m + 2) → K),
    Bchain a b c =
      bβ a (b (Fin.last (m + 1))) (c (Fin.last (m + 1))) (Bchain a (Fin.init b) (Fin.init c))

/-- **`m + 1` Bailey steps from the unit pair** (proved in `Cited/Assembly.lean` from
`Stmt_UnitPair`, `Stmt_BaileyLemma`, `Stmt_ChainStep` by induction on `m`):
`(Achain a b c, Bchain a b c)` is a Bailey pair relative to `a` at every level `n ≤ N`, provided
`a ≠ 0` and `(1+a-b_k)_N, (1+a-c_k)_N ≠ 0` for all `k`. -/
def Stmt_BPChain : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (a : K), a ≠ 0 → ∀ (N m : ℕ) (b c : Fin (m + 1) → K),
    (∀ k, rpoch (1 + a - b k) N ≠ 0) → (∀ k, rpoch (1 + a - c k) N ≠ 0) →
    ∀ n ≤ N, BP a (Achain a b c) (Bchain a b c) n

end Zeta2.Cited

end
