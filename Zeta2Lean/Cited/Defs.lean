import Zeta2Lean.Statements

/-!
# Zeta2Lean.Cited.Defs — definitions for discharging the two cited hypotheses

The main theorem `Zeta2.zeta2_7_9_11_not_all_rational` (`Zeta2Lean/Main.lean`, frozen) takes the
two cited hypotheses `PNT_Stmt` and `Andrews_Stmt` of `Zeta2Lean/Statements.lean` (frozen) as
parameters.  The `Cited` tree proves both, with the same blueprint pattern as the main development:

* `Cited/Defs.lean` (this file): the objects of the Andrews track (Bailey pairs at `q = 1`, one
  Bailey step, the iterated chain pair) and a small *proved* API (Pochhammer identities, `Fin.snoc`
  on chains) available to every proof file;
* `Cited/Statements.lean`: one `Prop` per sub-lemma (`Stmt_*`);
* `Cited/Assembly.lean`: `PNT_Stmt` and `Andrews_Stmt` from the sub-lemma `Prop`s (complete);
* `Cited/Proofs/*.lean`: one proof obligation per file, dependencies taken as hypotheses;
* `Cited/Vendor/PNT/*.lean`: the Wiener–Ikehara theorem, vendored from open Mathlib PRs;
* `Cited/Main.lean`: the unconditional main theorem and `#print axioms`.

The PNT track needs no new definitions (`Stmt_WienerIkehara` is stated with Mathlib's `LSeries`).

## The Andrews track (`q = 1` Bailey chain, "polynomial" normalisation)

`(x)_k = rpoch x k`.  A pair of sequences `(α, β)` is a *Bailey pair at level `n`* relative to `a`
(`BP a α β n`) if
```
  (1+a)_{2n} β_n = ∑_{r=0}^{n} α_r (1+a+n+r)_{n-r} / (n-r)!.
```
This is the classical `β_n = ∑_r α_r / ((n-r)! (1+a)_{n+r})` multiplied by `(1+a)_{2n}`:
the multiplied form never divides by `(1+a)_k`, which `Andrews_Stmt` does not assume non-zero
(it allows, e.g., `a = -1`).  One Bailey step with the pair `(ρ, σ)` maps `(α, β)` to
`(bα a ρ σ α, bβ a ρ σ β)`; `m + 1` steps with the pairs `(b k, c k)`, starting from the unit
pair `(unitα a, unitβ)`, give `(Achain a b c, Bchain a b c)`, and `Bchain` is (up to the
prefactor) the chain sum on the right of `Andrews_Stmt`.

Everything here is copied from the Andrews scout's complete, compiled proof (reference copy:
`docs/cited/AndrewsScout.lean`), with identical bodies, so its proofs apply verbatim.
-/

open Finset

noncomputable section

namespace Zeta2.Cited

/-! ## Pochhammer API (any commutative ring) -/

section Poch

variable {R : Type*} [CommRing R]

lemma rpoch_zero (x : R) : rpoch x 0 = 1 := by simp [rpoch]

lemma rpoch_one (x : R) : rpoch x 1 = x := by simp [rpoch]

lemma rpoch_succ (x : R) (k : ℕ) : rpoch x (k + 1) = rpoch x k * (x + k) := by
  simp [rpoch, Finset.prod_range_succ]

lemma rpoch_succ' (x : R) (k : ℕ) : rpoch x (k + 1) = x * rpoch (x + 1) k := by
  unfold rpoch
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
  rw [mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by ring)

/-- `(x)_{a+b} = (x)_a (x+a)_b`. -/
lemma rpoch_add (x : R) (a b : ℕ) : rpoch x (a + b) = rpoch x a * rpoch (x + a) b := by
  unfold rpoch
  rw [Finset.prod_range_add]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by push_cast; ring)

lemma map_rpoch {S : Type*} [CommRing S] (f : R →+* S) (x : R) (k : ℕ) :
    f (rpoch x k) = rpoch (f x) k := by
  simp [rpoch, map_prod]

/-- `(x)_κ ∣ (x)_N` for `κ ≤ N`, in the form used everywhere: `(x)_N ≠ 0 → (x)_κ ≠ 0`. -/
lemma rpoch_ne_zero_of_le (x : R) {N κ : ℕ} (h : rpoch x N ≠ 0) (hk : κ ≤ N) :
    rpoch x κ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [rpoch_add, h0, zero_mul]

/-- `(-N)_κ (N-κ)! = (-1)^κ N!` for `κ ≤ N`. -/
lemma rpoch_negN_mul (N κ : ℕ) (h : κ ≤ N) :
    rpoch (-(N : R)) κ * ((N - κ).factorial : R) = (-1) ^ κ * (N.factorial : R) := by
  induction κ with
  | zero => simp [rpoch_zero]
  | succ κ ih =>
    have h' : κ ≤ N := by omega
    have e : N - κ = (N - (κ + 1)) + 1 := by omega
    have ih' := ih h'
    rw [e, Nat.factorial_succ] at ih'
    rw [rpoch_succ, pow_succ]
    have e2 : ((N - (κ + 1) + 1 : ℕ) : R) = (N : R) - κ := by
      rw [← e, Nat.cast_sub h']
    push_cast at ih' e2
    linear_combination (-1 : R) * ih' + (rpoch (-(N : R)) κ * ((N - (κ + 1)).factorial : R)) * e2

/-- Reflection: `(x)_{N-κ} (1-x-N)_κ = (-1)^κ (x)_N` for `κ ≤ N`. -/
lemma rpoch_reflect (x : R) (N κ : ℕ) (h : κ ≤ N) :
    rpoch x (N - κ) * rpoch (1 - x - N) κ = (-1) ^ κ * rpoch x N := by
  induction κ with
  | zero => simp [rpoch_zero]
  | succ κ ih =>
    have h' : κ ≤ N := by omega
    have hN : N - κ = (N - (κ + 1)) + 1 := by omega
    have e1 : rpoch x (N - κ) = rpoch x (N - (κ + 1)) * (x + ((N - (κ + 1) : ℕ) : R)) := by
      rw [hN, rpoch_succ]
    have e2 : ((N - (κ + 1) : ℕ) : R) = (N : R) - κ - 1 := by
      rw [Nat.cast_sub (by omega : κ + 1 ≤ N)]
      push_cast
      ring
    rw [rpoch_succ, pow_succ,
      show (-1 : R) ^ κ * -1 * rpoch x N = -((-1) ^ κ * rpoch x N) by ring, ← ih h', e1, e2]
    ring

end Poch

lemma fact_ne {K : Type*} [Field K] [CharZero K] (n : ℕ) : (n.factorial : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-! ## Bailey pairs at `q = 1` (polynomial normalisation) -/

section Bailey

variable {K : Type*} [Field K]

/-- Bailey-pair relation relative to `a`, at level `n`:
`(1+a)_{2n} β_n = ∑_{r=0}^{n} α_r (1+a+n+r)_{n-r} / (n-r)!`. -/
def BP (a : K) (α β : ℕ → K) (n : ℕ) : Prop :=
  rpoch (1 + a) (2 * n) * β n =
    ∑ r ∈ range (n + 1), α r * rpoch (1 + a + n + r) (n - r) / ((n - r).factorial : K)

/-- The unit Bailey pair, `α` side: `α_r = (a+2r)/a · (a)_r (-1)^r / r!`. -/
def unitα (a : K) (r : ℕ) : K := (a + 2 * r) / a * rpoch a r * (-1) ^ r / (r.factorial : K)

/-- The unit Bailey pair, `β` side: `β_n = [n = 0]`. -/
def unitβ (n : ℕ) : K := if n = 0 then 1 else 0

/-- Bailey-lemma weight `(ρ)_j (σ)_j (1+a-ρ-σ)_{n-j} / ((1+a-ρ)_n (1+a-σ)_n (n-j)!)`. -/
def bw (a ρ σ : K) (n j : ℕ) : K :=
  rpoch ρ j * rpoch σ j * rpoch (1 + a - ρ - σ) (n - j) /
    (rpoch (1 + a - ρ) n * rpoch (1 + a - σ) n * ((n - j).factorial : K))

/-- New `α` after one Bailey step with the pair `(ρ, σ)`:
`α'_r = (ρ)_r (σ)_r / ((1+a-ρ)_r (1+a-σ)_r) · α_r`. -/
def bα (a ρ σ : K) (α : ℕ → K) (r : ℕ) : K :=
  rpoch ρ r * rpoch σ r / (rpoch (1 + a - ρ) r * rpoch (1 + a - σ) r) * α r

/-- New `β` after one Bailey step with the pair `(ρ, σ)`: `β'_n = ∑_{j ≤ n} bw a ρ σ n j · β_j`. -/
def bβ (a ρ σ : K) (β : ℕ → K) (n : ℕ) : K := ∑ j ∈ range (n + 1), bw a ρ σ n j * β j

end Bailey

/-! ## Chains: `Fin.snoc` API (proved) -/

section ChainAPI

lemma snoc_mem_chains {m n j : ℕ} {i' : Fin m → ℕ} (hi' : i' ∈ chains m j) (hj : j ≤ n) :
    (Fin.snoc i' j : Fin (m + 1) → ℕ) ∈ chains (m + 1) n := by
  rw [mem_chains] at hi' ⊢
  obtain ⟨hv, hmono⟩ := hi'
  refine ⟨fun k => ?_, fun a b hab => ?_⟩
  · induction k using Fin.lastCases with
    | last => simp [Fin.snoc_last, hj]
    | cast k => simp only [Fin.snoc_castSucc]; exact (hv k).trans hj
  · induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact le_rfl
      | cast a => simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact hv a
    | cast b =>
      induction a using Fin.lastCases with
      | last =>
        exfalso
        have h1 : (Fin.last m : ℕ) ≤ (Fin.castSucc b : ℕ) := hab
        simp at h1
        omega
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact hmono a b (Fin.castSucc_le_castSucc_iff.mp hab)

lemma init_mem_chains {m n : ℕ} {i : Fin (m + 1) → ℕ} (hi : i ∈ chains (m + 1) n) :
    Fin.init i ∈ chains m (i (Fin.last m)) := by
  rw [mem_chains] at hi ⊢
  obtain ⟨_, hmono⟩ := hi
  refine ⟨fun k => hmono _ _ (Fin.castSucc_lt_last k).le, fun a b hab => ?_⟩
  exact hmono _ _ (Fin.castSucc_le_castSucc_iff.mpr hab)

lemma chainPrev_snoc_castSucc {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) (k : Fin m) :
    chainPrev (Fin.snoc i' j : Fin (m + 1) → ℕ) k.castSucc = chainPrev i' k := by
  unfold chainPrev
  simp only [Fin.val_castSucc]
  split_ifs with h
  · rfl
  · have : (⟨(k : ℕ) - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨(k : ℕ) - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]

lemma chainPrev_snoc_last {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) :
    chainPrev (Fin.snoc i' j : Fin (m + 1) → ℕ) (Fin.last m) = chainLast i' := by
  unfold chainPrev chainLast
  simp only [Fin.val_last]
  split_ifs with h
  · rfl
  · have : (⟨m - 1, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨m - 1, by omega⟩ := rfl
    rw [this, Fin.snoc_castSucc]

lemma chainLast_snoc {m : ℕ} (i' : Fin m → ℕ) (j : ℕ) :
    chainLast (Fin.snoc i' j : Fin (m + 1) → ℕ) = j := by
  unfold chainLast
  simp only [Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
  exact Fin.snoc_last (α := fun _ => ℕ) (p := i') (x := j)

lemma chainLast_le {m N : ℕ} {i : Fin m → ℕ} (hi : i ∈ chains m N) : chainLast i ≤ N := by
  unfold chainLast
  split_ifs with h
  · exact Nat.zero_le _
  · exact (mem_chains.1 hi).1 _

end ChainAPI

/-! ## The iterated (chain) Bailey pair -/

section Chain

variable {K : Type*} [Field K]

/-- The `k`-th factor of the chain weight on the right of `Andrews_Stmt` (verbatim from there):
`(1+a-b_k-c_k)_{i_k-i_{k-1}} (b_{k+1})_{i_k} (c_{k+1})_{i_k}
  / ((i_k-i_{k-1})! (1+a-b_k)_{i_k} (1+a-c_k)_{i_k})`. -/
def chainFactor (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (i : Fin m → ℕ) (k : Fin m) : K :=
  rpoch (1 + a - b k.castSucc - c k.castSucc) (i k - chainPrev i k) *
      rpoch (b k.succ) (i k) * rpoch (c k.succ) (i k) /
    (((i k - chainPrev i k).factorial : K) * rpoch (1 + a - b k.castSucc) (i k) *
      rpoch (1 + a - c k.castSucc) (i k))

/-- `β` after `m + 1` Bailey steps with the pairs `(b k, c k)` (applied in the order
`k = 0, 1, …, m`), starting from `unitβ`, written as a chain sum:
`Bchain_n = ∑_{i ∈ chains m n} ∏_k chainFactor · (1+a-b_L-c_L)_{n-i_m}
  / ((1+a-b_L)_n (1+a-c_L)_n (n-i_m)!)`, `L = Fin.last m`. -/
def Bchain (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (n : ℕ) : K :=
  ∑ i ∈ chains m n, (∏ k : Fin m, chainFactor a b c i k) *
    (rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) (n - chainLast i) /
      (rpoch (1 + a - b (Fin.last m)) n * rpoch (1 + a - c (Fin.last m)) n *
        ((n - chainLast i).factorial : K)))

/-- `α` after `m + 1` Bailey steps, starting from `unitα a`:
`Achain_r = ∏_k (b_k)_r (c_k)_r / ((1+a-b_k)_r (1+a-c_k)_r) · unitα a r`. -/
def Achain (a : K) {m : ℕ} (b c : Fin (m + 1) → K) (r : ℕ) : K :=
  (∏ k, rpoch (b k) r * rpoch (c k) r / (rpoch (1 + a - b k) r * rpoch (1 + a - c k) r)) *
    unitα a r

end Chain

end Zeta2.Cited

end
