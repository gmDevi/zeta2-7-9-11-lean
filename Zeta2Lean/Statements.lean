import Zeta2Lean.Defs

/-!
# Zeta2Lean.Statements — one `Prop` per lemma of the blueprint

Every lemma of the proof is a `def Stmt_X : Prop` (or a `structure Stmt_X : Prop` with named
fields).  Proof files `Zeta2Lean/Proofs/*.lean` prove them, taking the statements they depend on
as *hypotheses*; `Zeta2Lean/Assembly.lean` derives the main theorem from the top-level ones;
`Zeta2Lean/Main.lean` wires everything together.

Two statements are *cited* (theorem parameters of the main theorem, never proved here):
* `PNT_Stmt` — the prime number theorem `ψ(x)/x → 1` (Chebyshev ψ from Mathlib; proved in Lean in
  the PrimeNumberTheoremAnd project, not yet in Mathlib).
* `Andrews_Stmt` — Andrews' multiple-series transformation of a terminating very-well-poised
  `₂ₘ₊₅F₂ₘ₊₄` (Andrews 1975, Thm 4, q → 1; Krattenthaler–Rivoal, Mém. AMS 186 (2007), Théorème 8),
  stated in full generality (any `m, N`, any field of characteristic 0, all denominators non-zero),
  i.e. as the identity of rational functions it is.  Tested numerically in `python/mirror.py`.

References "proof.md §x" are to the informal proof; "Lai" = arXiv:2304.00816, "LSZ" =
arXiv:2505.05005.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## Cited hypotheses -/

/-- **Prime number theorem** (cited): `ψ(x) / x → 1` where `ψ = Chebyshev.psi` is the second
Chebyshev function (`ψ n = log lcm(1,…,n)`, Mathlib `Chebyshev.psi_eq_log_lcmUpto`). -/
def PNT_Stmt : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)

/-- **Andrews' transformation** (cited; proof.md P6; Krattenthaler–Rivoal Théorème 8, q = 1 case of
Andrews 1975 Thm 4).  For `m, N ≥ 0`, with `b_k, c_k` indexed by `Fin (m+1)` (`b (Fin.last m) =
b_{m+1}`), and `(a/2+1)_κ/(a/2)_κ` written as `(a+2κ)/a`:
```
∑_{κ=0}^{N} (a+2κ)/a · (a)_κ/κ! · ∏_{k=1}^{m+1} (b_k)_κ (c_k)_κ / ((1+a-b_k)_κ (1+a-c_k)_κ)
            · (-N)_κ / (1+a+N)_κ
 = (1+a)_N (1+a-b_{m+1}-c_{m+1})_N / ((1+a-b_{m+1})_N (1+a-c_{m+1})_N)
   · ∑_{0 ≤ i_1 ≤ … ≤ i_m ≤ N} (-N)_{i_m} / (b_{m+1}+c_{m+1}-a-N)_{i_m}
       · ∏_{k=1}^{m} (1+a-b_k-c_k)_{i_k-i_{k-1}} (b_{k+1})_{i_k} (c_{k+1})_{i_k}
                     / ((i_k-i_{k-1})! (1+a-b_k)_{i_k} (1+a-c_k)_{i_k})
```
(`i_0 = 0`), valid in every field of characteristic zero whenever all displayed denominators are
non-zero (the hypotheses below imply this, since `(x)_κ ∣ (x)_N` for `κ ≤ N`). -/
def Andrews_Stmt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m N : ℕ) (a : K) (b c : Fin (m + 1) → K),
    a ≠ 0 →
    (∀ k, rpoch (1 + a - b k) N ≠ 0) →
    (∀ k, rpoch (1 + a - c k) N ≠ 0) →
    rpoch (1 + a + N) N ≠ 0 →
    rpoch (b (Fin.last m) + c (Fin.last m) - a - N) N ≠ 0 →
    (∑ κ ∈ range (N + 1),
        (a + 2 * κ) / a * (rpoch a κ / (κ.factorial : K)) *
        (∏ k, rpoch (b k) κ * rpoch (c k) κ / (rpoch (1 + a - b k) κ * rpoch (1 + a - c k) κ)) *
        (rpoch (-(N : K)) κ / rpoch (1 + a + N) κ))
    = rpoch (1 + a) N * rpoch (1 + a - b (Fin.last m) - c (Fin.last m)) N /
        (rpoch (1 + a - b (Fin.last m)) N * rpoch (1 + a - c (Fin.last m)) N) *
      ∑ i ∈ chains m N,
        rpoch (-(N : K)) (chainLast i) /
            rpoch (b (Fin.last m) + c (Fin.last m) - a - N) (chainLast i) *
          ∏ k : Fin m,
            rpoch (1 + a - b k.castSucc - c k.castSucc) (i k - chainPrev i k) *
                rpoch (b k.succ) (i k) * rpoch (c k.succ) (i k) /
              (((i k - chainPrev i k).factorial : K) * rpoch (1 + a - b k.castSucc) (i k) *
                rpoch (1 + a - c k.castSucc) (i k))

/-! ## The main statement -/

/-- **Main theorem** (target): the Riemann sums defining every `J s` converge, and `ζ₂(7)`,
`ζ₂(9)`, `ζ₂(11)` are not all rational. -/
def MainStatement : Prop :=
  (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
    ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q))

/-! ## Volkenborn integral (proof.md P1, P2) -/

/-- The Riemann sums of `(x+1/2)^{-s}` converge (to `J s`), for every `s`. -/
def Stmt_JConv : Prop :=
  ∀ s : ℕ, HasVolkenborn (halfPow s) (J s)

/-- Translation (proof.md P1; LSZ Lemma 2.4) for `f(t) = (t+1/2)^{-s}`, `f' = -s (t+1/2)^{-s-1}`:
`∫ f(t+k) dt = ∫ f(t) dt - s ∑_{ℓ<k} (ℓ+1/2)^{-s-1}`. -/
def Stmt_Translation : Prop :=
  ∀ (s k : ℕ) (I : ℚ_[2]), HasVolkenborn (halfPow s) I →
    HasVolkenborn (fun x => halfPow s (x + k)) (I - (s : ℚ_[2]) * ∑ l ∈ range k, halfPow (s + 1) l)

/-- Lai's irrationality criterion (proof.md P4; Lai Lemma 2.1). -/
def Stmt_Criterion : Prop :=
  ∀ (k : ℕ) (α : Fin k → ℚ_[2]) (a₀ : ℕ → ℤ) (a : ℕ → Fin k → ℤ) (B : ℕ → ℝ),
    (∀ m, |(a₀ m : ℝ)| ≤ B m) → (∀ m j, |(a m j : ℝ)| ≤ B m) →
    (∃ᶠ m in atTop, (a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j ≠ 0) →
    Tendsto (fun m => B m * ‖(a₀ m : ℚ_[2]) + ∑ j, (a m j : ℚ_[2]) * α j‖) atTop (𝓝 0) →
    ¬ ∀ j, ∃ q : ℚ, α j = q

/-! ## Partial fractions and the linear form (proof.md §3) -/

/-- Partial fractions: `R_n(t) = ∑_{i=1}^{8} ∑_{k=0}^{n} r_{i,k} (t+k)^{-i}`, as a polynomial
identity after multiplying by `(t)_{n+1}^8`, and as an identity of Taylor expansions at every
non-pole `y`. -/
structure Stmt_PF : Prop where
  poly : ∀ n : ℕ, Rnum n = PFpoly n
  series : ∀ (n : ℕ) (y : ℚ), (∀ j ≤ n, y + (j : ℚ) ≠ 0) →
    Rser n y = ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1), C (rcoef n i k) * ((C (y + k) + X) ^ i)⁻¹

/-- Vanishing sums (proof.md Lemma 1): the symmetry `r_{i,n-k} = (-1)^{i+1} r_{i,k}` (from
`R_n(-t-n) = -R_n(t)`), `c₁ = 0` (degree `R_n = -7`) and `c_i = 0` for even `i`. -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ n i k : ℕ, k ≤ n → rcoef n i (n - k) = (-1) ^ (i + 1) * rcoef n i k
  c1 : ∀ n : ℕ, csum n 1 = 0
  ceven : ∀ n i : ℕ, Even i → csum n i = 0

/-- **L1** (proof.md Lemma 1): `S_n = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ + 504 c₇ J₁₀`
`(= ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9) + Z₁₁ ζ₂(11))`, with convergence of the Riemann sums. -/
def Stmt_L1 : Prop :=
  ∀ n : ℕ, HasVolkenborn (fun x => ((integrand n x : ℚ) : ℚ_[2]))
    ((rho0 n : ℚ_[2]) + 60 * (csum n 3 : ℚ_[2]) * J 6 + 210 * (csum n 5 : ℚ_[2]) * J 8 +
      504 * (csum n 7 : ℚ_[2]) * J 10)

/-! ## Denominators (proof.md §4) -/

/-- Building block (proof.md P5 for `F(t) = 2^{2n}(t+1/2)_n/n!` at `t = -k`):
`4^n (1/2-ε)_k (1/2+ε)_{n-k} / n!` has `d_n^j [ε^j] ∈ ℤ` for all `j`. -/
def Stmt_BlockF : Prop :=
  ∀ n k : ℕ, k ≤ n → ∀ j : ℕ, ∃ z : ℤ,
    (dn n : ℚ) ^ j * coeff j (C ((4 : ℚ) ^ n / (n.factorial : ℚ)) * psPoch (1 / 2) (-1) k *
      psPoch (1 / 2) 1 (n - k)) = z

/-- **L2a** (proof.md §4.1): `d_n^{8-i} r_{i,k} ∈ ℤ`. -/
def Stmt_L2a : Prop :=
  ∀ n i k : ℕ, 1 ≤ i → i ≤ 8 → k ≤ n → ∃ z : ℤ, (dn n : ℚ) ^ (8 - i) * rcoef n i k = z

/-- **L2b** (proof.md §4.2, root trick): `d_n^{12} ρ₀ ∈ ℤ`. -/
def Stmt_L2b : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, (dn n : ℚ) ^ 12 * rho0 n = z

/-- Residue form (proof.md §4.3 Step 1): `ρ₀ = -24 ∑_{ℓ=1}^{n} [ε^7] T_{n,ℓ}(ε)`. -/
def Stmt_ResidueForm : Prop :=
  ∀ n : ℕ, rho0 n = -24 * ∑ l ∈ Icc 1 n, coeff 7 (Tser n l)

/-- Andrews applied (proof.md §4.3 Steps 2–3): `T_{n,ℓ}(ε) = ∑_{0 ≤ J₁ ≤ ⋯ ≤ J₈ ≤ n-ℓ} F_J(ε)`. -/
def Stmt_AndrewsApplied : Prop :=
  ∀ n l : ℕ, 1 ≤ l → l ≤ n → Tser n l = ∑ ch ∈ chains 8 (n - l), Fser n l ch

/-- Closed form of `F_J(0)` (proof.md §4.3 Step 4). -/
def Stmt_FJClosed : Prop :=
  ∀ (n l : ℕ) (ch : Fin 8 → ℕ), 1 ≤ l → l ≤ n → ch ∈ chains 8 (n - l) →
    constantCoeff (Fser n l ch) = FJ0 n l ch

/-- One-power saving at `ε = 0` (proof.md §4.3 Step 5, Kummer): `v_p(F_J(0)) ≥ -4` for primes
`p ≥ 11` with `p² > 2n`. -/
def Stmt_FJKummer : Prop :=
  ∀ (n l : ℕ) (ch : Fin 8 → ℕ) (p : ℕ), p.Prime → 11 ≤ p → 2 * n < p ^ 2 → 1 ≤ l → l ≤ n →
    ch ∈ chains 8 (n - l) → -4 ≤ padicValRat p (FJ0 n l ch)

/-- **L2c** (proof.md §4.3): `v_p(ρ₀) ≥ -11` for primes `p ≥ 11` with `p² > 2n`. -/
def Stmt_L2c : Prop :=
  ∀ n p : ℕ, p.Prime → 11 ≤ p → 2 * n < p ^ 2 → -11 ≤ padicValRat p (rho0 n)

/-- **L2 corollary** (proof.md §4.4): `D_n = d_n^{12}/Φ_n` clears all denominators. -/
def Stmt_L2cor : Prop :=
  ∀ n : ℕ, ∃ a : Fin 4 → ℤ,
    (Dn n : ℚ) * rho0 n = a 0 ∧ (Dn n : ℚ) * Z7 n = a 1 ∧ (Dn n : ℚ) * Z9 n = a 2 ∧
      (Dn n : ℚ) * Z11 n = a 3

/-! ## Archimedean size and asymptotics (proof.md §6, §8) -/

/-- **L4** (proof.md §6): `max(|ρ₀|, |Z₇|, |Z₉|, |Z₁₁|) ≤ C (n+1)^A 2^{16n}` for some constants
(proof.md: `C = 3.4·10⁸`, `A = 2`; any constants will do). -/
def Stmt_L4 : Prop :=
  ∃ (Cst : ℝ) (A : ℕ), ∀ n : ℕ,
    |(rho0 n : ℝ)| ≤ archBound Cst A n ∧ |(Z7 n : ℝ)| ≤ archBound Cst A n ∧
      |(Z9 n : ℝ)| ≤ archBound Cst A n ∧ |(Z11 n : ℝ)| ≤ archBound Cst A n

/-- The exponent computation of proof.md §8 (uses PNT): along `n = 2^m - 1`,
`D_n · C (n+1)^A 2^{16n} · 2^{-(32n+14-11m)} → 0` (exponent `11 - 16 log 2 < 0`). -/
def Stmt_Asymptotic : Prop :=
  PNT_Stmt → ∀ (Cst : ℝ) (A : ℕ),
    Tendsto (fun m : ℕ => (Dn (2 ^ m - 1) : ℝ) * archBound Cst A (2 ^ m - 1) * (2 : ℝ) ^ (-target m))
      atTop (𝓝 0)

/-! ## 2-adic Δ-calculus (proof.md P3; Lai Lemmas 2.4, 2.5; LSZ Lemmas 2.5, 2.6) -/

/-- The general Δ-calculus, in Riemann-sum form (no convergence assumptions needed). -/
structure Stmt_Delta : Prop where
  /-- Lai Lemma 2.4 (2.3), Riemann-sum form: `Δ_m(f) ≥ c ⇒ R_M ≡ R_m mod 2^{c-1}` (`M ≥ m`). -/
  riemann : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaGe m c f →
    ∀ M, m ≤ M → ‖volkenbornSum f M - volkenbornSum f m‖ ≤ (2 : ℝ) ^ (1 - c)
  /-- Lai Lemma 2.4 (2.2), Riemann-sum form: `Δ(f) ≥ c ⇒ v₂(R_M) ≥ c - 1`. -/
  riemannAll : ∀ (f : ℕ → ℚ_[2]) (c : ℤ), DeltaAll c f →
    ∀ M, ‖volkenbornSum f M‖ ≤ (2 : ℝ) ^ (1 - c)
  mono : ∀ (f : ℕ → ℚ_[2]) (m m' : ℕ) (c c' : ℤ), m ≤ m' → c' ≤ c → DeltaGe m c f → DeltaGe m' c' f
  monoAll : ∀ (f : ℕ → ℚ_[2]) (c c' : ℤ), c' ≤ c → DeltaAll c f → DeltaAll c' f
  ofAll : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), DeltaAll c f → DeltaGe m c f
  /-- Lai Lemma 2.5 / LSZ 2.6(a) (finite sums). -/
  sum : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (m : ℕ) (c : ℤ),
    (∀ i ∈ s, DeltaGe m c (F i)) → DeltaGe m c (fun x => ∑ i ∈ s, F i x)
  sumAll : ∀ {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (c : ℤ),
    (∀ i ∈ s, DeltaAll c (F i)) → DeltaAll c (fun x => ∑ i ∈ s, F i x)
  /-- LSZ 2.6(b) (constant factor; only `≥` is needed). -/
  smul : ∀ (f : ℕ → ℚ_[2]) (m : ℕ) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaGe m c f → DeltaGe m (c + e) (fun x => a * f x)
  smulAll : ∀ (f : ℕ → ℚ_[2]) (c e : ℤ) (a : ℚ_[2]), ‖a‖ ≤ (2 : ℝ) ^ (-e) →
    DeltaAll c f → DeltaAll (c + e) (fun x => a * f x)
  /-- Lai Lemma 2.5(2) (products of `ℤ₂`-valued functions). -/
  mul : ∀ (f g : ℕ → ℚ_[2]) (m : ℕ) (c : ℤ), IntValued f → IntValued g →
    DeltaGe m c f → DeltaGe m c g → DeltaGe m c (fun x => f x * g x)
  mulAll : ∀ (f g : ℕ → ℚ_[2]) (c : ℤ), IntValued f → IntValued g →
    DeltaAll c f → DeltaAll c g → DeltaAll c (fun x => f x * g x)

/-- Δ-bounds for the concrete building functions (proof.md P3(d),(e); Lai Lemma 2.5(1),(3)). -/
structure Stmt_DeltaFun : Prop where
  /-- `Δ(C(t+j, N)) ≥ -⌊log₂ N⌋`. -/
  binom : ∀ j N : ℕ, DeltaAll (-(Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]))
  /-- `Δ_m(C(t+j, N)^2) ≥ 1 - ⌊log₂ N⌋` for `m > ⌊log₂ N⌋`. -/
  binomSq : ∀ j N m : ℕ, Nat.log 2 N < m →
    DeltaGe m (1 - (Nat.log 2 N : ℤ)) (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2]) ^ 2)
  /-- `h_β` is `ℤ₂`-valued ... -/
  hcoefInt : ∀ n β : ℕ, IntValued (fun x => ((hcoef n β x : ℚ) : ℚ_[2]))
  /-- ... with `Δ(h_β) ≥ 0` (it is a polynomial in the `1/(2x+2k+1)` with integer coefficients). -/
  hcoefDelta : ∀ n β : ℕ, DeltaAll 0 (fun x => ((hcoef n β x : ℚ) : ℚ_[2]))

/-- Lai's digit lemma (proof.md P7; Lai Lemma 6.1) and `v₂((2^m-1)!) = 2^m - 1 - m`, for
`n = 2^m - 1`, `k₀ = 2^{m-1}`. -/
structure Stmt_Digit : Prop where
  fact : ∀ m : ℕ, padicValNat 2 (2 ^ m - 1).factorial = 2 ^ m - 1 - m
  dom : ∀ m : ℕ, 2 ≤ m →
    padicValNat 2 ((2 ^ (m - 1) - 1).factorial * (2 ^ m - 1 - 2 ^ (m - 1)).factorial) = 2 ^ m - 2 * m
  other : ∀ m : ℕ, 2 ≤ m → ∀ l : ℕ, 1 ≤ l → l ≤ 2 ^ m - 1 → l ≠ 2 ^ (m - 1) →
    2 ^ m + 1 - 2 * m ≤ padicValNat 2 ((l - 1).factorial * (2 ^ m - 1 - l).factorial)

/-! ## Nonvanishing along `n = 2^m - 1` (proof.md §7, L5) -/

/-- Leibniz expansion of `integrand n x = -R_n'''(x+1/2) = -6 · 2^{24n+8} [ε^3] f(x+ε)`,
`f(t) = (2t+1+n) (t+1)_n^8 ∏_{k≤n} (2t+2k+1)^{-8}` (proof.md §7 "Leibniz"). -/
def Stmt_Leibniz : Prop :=
  ∀ n x : ℕ, integrand n x =
    ∑ γ ∈ range 2, ∑ β ∈ range (4 - γ), ∑ M ∈ (Icc 1 n).finsuppAntidiag (3 - γ - β),
      leibTerm n γ β M x

/-- Δ-bound for each Leibniz term, `n = 2^m - 1` (proof.md §7 "All other terms"):
`Δ ≥ 32n + 13 - 11m + βm + ∑_l v₂ C(8, M l) + #{multiset elements ≠ k₀}`. -/
def Stmt_LeibTermBound : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ γ β : ℕ, γ ≤ 1 → γ + β ≤ 3 →
    ∀ M ∈ (Icc 1 (2 ^ m - 1)).finsuppAntidiag (3 - γ - β),
      DeltaAll (32 * ((2 : ℤ) ^ m - 1) + 13 - 11 * (m : ℤ) + (β : ℤ) * m +
          ∑ l ∈ Icc 1 (2 ^ m - 1), (padicValNat 2 (Nat.choose 8 (M l)) : ℤ) +
          ∑ l ∈ (Icc 1 (2 ^ m - 1)).erase (2 ^ (m - 1)), (M l : ℤ))
        (fun x => ((leibTerm (2 ^ m - 1) γ β M x : ℚ) : ℚ_[2]))

/-- The dominant term (proof.md §7 "Dominant term"): `Δ_m ≥ target + 2`, and its level-`m`
Riemann sum has valuation exactly `target m = 32n + 14 - 11m`. -/
def Stmt_L5Dom : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    DeltaGe m (target m + 2) (fun x => ((domTerm m x : ℚ) : ℚ_[2])) ∧
      ‖volkenbornSum (fun x => ((domTerm m x : ℚ) : ℚ_[2])) m‖ = (2 : ℝ) ^ (-target m)

/-- **L5** (proof.md §7): for `n = 2^m - 1`, `m ≥ 2`, `v₂(S_n) = 32n + 14 - 11m`; in particular
`S_n ≠ 0`. -/
def Stmt_L5 : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∀ I : ℚ_[2],
    HasVolkenborn (fun x => ((integrand (2 ^ m - 1) x : ℚ) : ℚ_[2])) I → ‖I‖ = (2 : ℝ) ^ (-target m)

end Zeta2

end
