import Mathlib

/-!
# Zeta2Lean.Defs — every definition of the project

Target: at least one of `ζ₂(7), ζ₂(9), ζ₂(11)` is irrational (informal proof: `proof.md`, §§2–8;
map of statements: `BLUEPRINT.md`).  All objects of the proof are defined here, once, so that the
~20 proof files can be elaborated independently.

Conventions.
* `ℚ_[2]` is Mathlib's field of 2-adic numbers; `‖·‖` its norm (`‖2‖ = 1/2`).
* The Volkenborn integral (proof.md P1) is *not* in Mathlib.  We use Riemann sums
  `volkenbornSum f N = 2^{-N} ∑_{x<2^N} f x` and the predicate `HasVolkenborn f I`
  (`volkenbornSum f N → I`).  `volkenborn f = limUnder …` is only a name for the limit; every
  statement that uses a value comes with a `HasVolkenborn` certificate.
* `J s = ∫_{ℤ₂} (t+1/2)^{-s} dt` and `zeta2 s = J (s-1) / ((s-1) 2^s)`.  The identification of
  `zeta2 s` with the Kubota–Leopoldt value `L₂(s, ω^{1-s})` is LSZ Lemma 2.8 (cited, not
  formalised).  Irrationality is invariant under the non-zero rational factor `(s-1) 2^s`, so the
  theorem about `J 6, J 8, J 10` *is* the theorem.
* The construction (proof.md §3): `R_n(t) = 2^{16n} (2t+n) (t+1/2)_n^8 / (t)_{n+1}^8`,
  `R_n(t) = ∑_{i=1}^{8} ∑_{k=0}^{n} r_{i,k} (t+k)^{-i}`.  The coefficients are defined by the
  explicit Taylor formula `r_{8-μ,k} = [ε^μ] G_k(ε)`, `G_k(ε) = ε^8 R_n(-k+ε)
  = 2^{16n} (n-2k+2ε) Ψ_k(ε)^8`, `Ψ_k(ε) = (1/2-ε)_k (1/2+ε)_{n-k} / ((1-ε)_k (1+ε)_{n-k})`,
  computed in `PowerSeries ℚ` (all denominators have non-zero constant term, so `⁻¹` is the
  honest inverse).  That these are the partial-fraction coefficients of `R_n` is `Stmt_PF`.
* The linear form is `S_n = ∫ integrand n`, `integrand n x = ∑_{i,k} (i)_3 r_{i,k} (x+k+1/2)^{-i-3}`
  (`= -R_n'''(x+1/2)`), and `S_n = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ + 504 c₇ J₁₀
  = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9) + Z₁₁ ζ₂(11)` (`Stmt_L1`).
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ## Volkenborn integral via Riemann sums (proof.md P1, P2) -/

/-- Riemann sum `2^{-N} ∑_{x < 2^N} f x` of the Volkenborn integral. -/
def volkenbornSum (f : ℕ → ℚ_[2]) (N : ℕ) : ℚ_[2] :=
  ((2 : ℚ_[2]) ^ N)⁻¹ * ∑ x ∈ range (2 ^ N), f x

/-- `f` is Volkenborn integrable with integral `I`: the Riemann sums converge 2-adically to `I`. -/
def HasVolkenborn (f : ℕ → ℚ_[2]) (I : ℚ_[2]) : Prop :=
  Tendsto (volkenbornSum f) atTop (𝓝 I)

/-- The Volkenborn integral.  Only ever used together with a `HasVolkenborn` certificate
(`Stmt_JConv` proves convergence for every `J s`). -/
def volkenborn (f : ℕ → ℚ_[2]) : ℚ_[2] :=
  limUnder atTop (volkenbornSum f)

/-- `halfPow s x = (x + 1/2)^{-s}`, an element of `ℚ_[2]` (a 2-adic integer times `2^s`). -/
def halfPow (s x : ℕ) : ℚ_[2] :=
  ((x : ℚ_[2]) + 2⁻¹)⁻¹ ^ s

/-- `J s = ∫_{ℤ₂} (t + 1/2)^{-s} dt` (proof.md P2). -/
def J (s : ℕ) : ℚ_[2] :=
  volkenborn (halfPow s)

/-- The 2-adic zeta value, normalised by LSZ Lemma 2.8: `J_{s-1} = (s-1) 2^s ζ₂(s)` (`s ≥ 2`).
E.g. `zeta2 7 = J 6 / 768`, `zeta2 9 = J 8 / 4096`, `zeta2 11 = J 10 / 20480`. -/
def zeta2 (s : ℕ) : ℚ_[2] :=
  J (s - 1) / (((s : ℚ_[2]) - 1) * 2 ^ s)

/-! ## Pochhammer symbols -/

/-- Rising factorial `(x)_k = x (x+1) ⋯ (x+k-1)` in any commutative ring. -/
def rpoch {K : Type*} [CommRing K] (x : K) (k : ℕ) : K :=
  ∏ j ∈ range k, (x + j)

/-- `(c + d ε)_k = ∏_{j<k} (c + j + d ε)` as a power series in `ε` (a polynomial). -/
def psPoch (c d : ℚ) (k : ℕ) : PowerSeries ℚ :=
  ∏ j ∈ range k, (C (c + j) + C d * X)

/-! ## The construction (proof.md §3) -/

/-- `Ψ_k(ε) = (1/2-ε)_k (1/2+ε)_{n-k} / ((1-ε)_k (1+ε)_{n-k})`. -/
def Psi (n k : ℕ) : PowerSeries ℚ :=
  psPoch (1 / 2) (-1) k * psPoch (1 / 2) 1 (n - k) * (psPoch 1 (-1) k * psPoch 1 1 (n - k))⁻¹

/-- `G_k(ε) = ε^8 R_n(-k+ε) = 2^{16n} (n - 2k + 2ε) Ψ_k(ε)^8` (proof.md §3, "useful formula"). -/
def Gser (n k : ℕ) : PowerSeries ℚ :=
  C ((2 : ℚ) ^ (16 * n)) * (C ((n : ℚ) - 2 * k) + C 2 * X) * Psi n k ^ 8

/-- Partial-fraction coefficient `r_{i,k}` of `R_n` (`1 ≤ i ≤ 8`, `0 ≤ k ≤ n`), `0` otherwise:
`r_{8-μ,k} = [ε^μ] G_k(ε)`. -/
def rcoef (n i k : ℕ) : ℚ :=
  if 1 ≤ i ∧ i ≤ 8 ∧ k ≤ n then coeff (8 - i) (Gser n k) else 0

/-- `c_i = ∑_k r_{i,k}`. -/
def csum (n i : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), rcoef n i k

/-- `A_k^{(s)} = ∑_{ℓ=0}^{k-1} (ℓ + 1/2)^{-s} = ∑_{ℓ=1}^{k} (ℓ - 1/2)^{-s}`. -/
def Ahalf (k s : ℕ) : ℚ :=
  ∑ l ∈ range k, (((l : ℚ) + 1 / 2)⁻¹) ^ s

/-- `ρ₀ = - ∑_{i=1}^{8} ∑_{k=0}^{n} (i)_4 r_{i,k} A_k^{(i+4)}` (proof.md Lemma 1). -/
def rho0 (n : ℕ) : ℚ :=
  -∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
      ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n i k * Ahalf k (i + 4)

/-- `Z₇ = (3)_4 2^7 c₃ = 46080 c₃`. -/
def Z7 (n : ℕ) : ℚ := 46080 * csum n 3

/-- `Z₉ = (5)_4 2^9 c₅ = 860160 c₅`. -/
def Z9 (n : ℕ) : ℚ := 860160 * csum n 5

/-- `Z₁₁ = (7)_4 2^11 c₇ = 10321920 c₇`. -/
def Z11 (n : ℕ) : ℚ := 10321920 * csum n 7

/-- The integrand `f_n(x) = ∑_{i,k} (i)_3 r_{i,k} (x + k + 1/2)^{-i-3} = -R_n'''(x + 1/2)`
(values at `x ∈ ℕ`, rational). -/
def integrand (n x : ℕ) : ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
    ((i : ℚ) * (i + 1) * (i + 2)) * rcoef n i k * ((((x + k : ℕ) : ℚ) + 1 / 2)⁻¹) ^ (i + 3)

/-- `S_n = -∫_{ℤ₂} R_n'''(t + 1/2) dt`. -/
def Sn (n : ℕ) : ℚ_[2] :=
  volkenborn (fun x => ((integrand n x : ℚ) : ℚ_[2]))

/-! ## Partial fractions (the product form of `R_n`) -/

/-- Numerator `2^{16n} (2t+n) (t+1/2)_n^8` of `R_n` as a polynomial in `t`. -/
def Rnum (n : ℕ) : Polynomial ℚ :=
  Polynomial.C ((2 : ℚ) ^ (16 * n)) * (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ)) *
    (∏ j ∈ range n, (Polynomial.X + Polynomial.C ((j : ℚ) + 1 / 2))) ^ 8

/-- `(t)_{n+1}^8 · ∑_{i,k} r_{i,k} (t+k)^{-i}` as a polynomial in `t`. -/
def PFpoly (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Icc (1 : ℕ) 8, ∑ k ∈ range (n + 1),
    Polynomial.C (rcoef n i k) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (8 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 8

/-- The Taylor expansion `ε ↦ R_n(y + ε)` (meaningful when `y ∉ {0, -1, …, -n}`). -/
def Rser (n : ℕ) (y : ℚ) : PowerSeries ℚ :=
  C ((2 : ℚ) ^ (16 * n)) * (C (2 * y + n) + C 2 * X) * (∏ j ∈ range n, (C (y + 1 / 2 + j) + X)) ^ 8 *
    ((∏ j ∈ range (n + 1), (C (y + j) + X)) ^ 8)⁻¹

/-! ## Denominators (proof.md §4) -/

/-- `d_n = lcm(1, …, n)` (Mathlib's `Nat.lcmUpto`). -/
def dn (n : ℕ) : ℕ := Nat.lcmUpto n

/-- `Φ_n = ∏_{p prime, max(√(2n), 10) < p ≤ n} p` (proof.md §4.4). -/
def Phi (n : ℕ) : ℕ :=
  ∏ p ∈ (range (n + 1)).filter (fun p => p.Prime ∧ 11 ≤ p ∧ 2 * n < p ^ 2), p

/-- `D_n = d_n^{12} / Φ_n` (exact division: `Φ_n ∣ d_n`). -/
def Dn (n : ℕ) : ℕ := dn n ^ 12 / Phi n

/-! ### Objects of the Andrews argument for L2c (proof.md §4.3) -/

/-- `T_{n,ℓ}(ε) = 2^{16n} (ℓ-1/2-ε)^3 (1/2-ε)_{ℓ-1}^8 ∑_{k=ℓ}^{n} (n-2k+2ε) (ℓ+1/2-ε)_{k-ℓ}^8
(1/2+ε)_{n-k}^8 / ((1-ε)_k^8 (1+ε)_{n-k}^8)`  (proof.md §4.3 Step 1). -/
def Tser (n l : ℕ) : PowerSeries ℚ :=
  C ((2 : ℚ) ^ (16 * n)) * (C ((l : ℚ) - 1 / 2) - X) ^ 3 * psPoch (1 / 2) (-1) (l - 1) ^ 8 *
    ∑ k ∈ Icc l n, (C ((n : ℚ) - 2 * k) + C 2 * X) * psPoch ((l : ℚ) + 1 / 2) (-1) (k - l) ^ 8 *
      psPoch (1 / 2) 1 (n - k) ^ 8 * (psPoch 1 (-1) k ^ 8 * psPoch 1 1 (n - k) ^ 8)⁻¹

/-- Chains `0 ≤ i₁ ≤ i₂ ≤ ⋯ ≤ i_m ≤ N`, encoded as monotone `i : Fin m → ℕ` with values `≤ N`
(`i ⟨k-1,_⟩ = i_k`). -/
def chains (m N : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun _ : Fin m => range (N + 1)).filter
    (fun i => ∀ a b : Fin m, a ≤ b → i a ≤ i b)

/-- `i_{k-1}` for the chain `i` at position `k` (with `i₀ = 0`). -/
def chainPrev {m : ℕ} (i : Fin m → ℕ) (k : Fin m) : ℕ :=
  if h : (k : ℕ) = 0 then 0 else i ⟨(k : ℕ) - 1, by omega⟩

/-- The last entry `i_m` of a chain (`0` for the empty chain). -/
def chainLast {m : ℕ} (i : Fin m → ℕ) : ℕ :=
  if h : m = 0 then 0 else i ⟨m - 1, by omega⟩

/-- `P_ℓ(ε) = 2^{16n} (ℓ-1/2-ε)^3 (1/2-ε)_{ℓ-1}^8 (1/2+ε)_N^8 / ((1-ε)_ℓ^8 (1+ε)_N^8)`, `N = n-ℓ`
(proof.md §4.3 Step 2). -/
def Pser (n l : ℕ) : PowerSeries ℚ :=
  C ((2 : ℚ) ^ (16 * n)) * (C ((l : ℚ) - 1 / 2) - X) ^ 3 * psPoch (1 / 2) (-1) (l - 1) ^ 8 *
    psPoch (1 / 2) 1 (n - l) ^ 8 * (psPoch 1 (-1) l ^ 8 * psPoch 1 1 (n - l) ^ 8)⁻¹

/-- The Andrews summand `F_J(ε)` of proof.md §4.3 Step 3 (`J = ch`, a chain of length 8 in
`[0, N]`, `N = n - ℓ`, `d_i = J_i - J_{i-1}`):
`F_J = -(N+1)(ℓ-2ε) P_ℓ ∏_{i=1}^{8} (1/2)_{d_i}/d_i!
  ∏_{i=1}^{7} (-N-ε)_{J_i}(ℓ+1/2-ε)_{J_i} / ((ℓ+1-ε)_{J_i}(1/2-N-ε)_{J_i})
  · (ℓ+1-2ε)_{J_8} (-N)_{J_8} / ((J_8+1)(ℓ+1-ε)_{J_8}(1/2-N-ε)_{J_8})`. -/
def Fser (n l : ℕ) (ch : Fin 8 → ℕ) : PowerSeries ℚ :=
  C (-((n - l : ℕ) : ℚ) - 1) * (C (l : ℚ) - C 2 * X) * Pser n l *
    (∏ i : Fin 8, C (rpoch (1 / 2 : ℚ) (ch i - chainPrev ch i) / ((ch i - chainPrev ch i).factorial : ℚ))) *
    (∏ i : Fin 7,
      psPoch (-((n - l : ℕ) : ℚ)) (-1) (ch i.castSucc) * psPoch ((l : ℚ) + 1 / 2) (-1) (ch i.castSucc) *
        (psPoch ((l : ℚ) + 1) (-1) (ch i.castSucc) *
          psPoch (1 / 2 - ((n - l : ℕ) : ℚ)) (-1) (ch i.castSucc))⁻¹) *
    (psPoch ((l : ℚ) + 1) (-2) (ch 7) * C (rpoch (-((n - l : ℕ) : ℚ)) (ch 7)) *
      (C ((ch 7 : ℚ) + 1) * psPoch ((l : ℚ) + 1) (-1) (ch 7) *
        psPoch (1 / 2 - ((n - l : ℕ) : ℚ)) (-1) (ch 7))⁻¹)

/-- Closed form of `F_J(0)` (proof.md §4.3 Step 4):
`-64 (2ℓ-1)^{-4} C(2ℓ-2,ℓ-1) (N+1)/(J_8+1) ∏_{i≤8} C(2d_i,d_i) ∏_{i≤7} C(2(ℓ+J_i),ℓ+J_i)
∏_{i≤8} C(2(N-J_i),N-J_i)`. -/
def FJ0 (n l : ℕ) (ch : Fin 8 → ℕ) : ℚ :=
  -64 / (2 * (l : ℚ) - 1) ^ 4 * ((Nat.choose (2 * l - 2) (l - 1) : ℕ) : ℚ) *
    (((n - l : ℕ) : ℚ) + 1) / ((ch 7 : ℚ) + 1) *
    (∏ i : Fin 8, ((Nat.choose (2 * (ch i - chainPrev ch i)) (ch i - chainPrev ch i) : ℕ) : ℚ)) *
    (∏ i : Fin 7, ((Nat.choose (2 * (l + ch i.castSucc)) (l + ch i.castSucc) : ℕ) : ℚ)) *
    (∏ i : Fin 8, ((Nat.choose (2 * (n - l - ch i)) (n - l - ch i) : ℕ) : ℚ))

/-! ## Archimedean size (proof.md §6) -/

/-- The shape `C (n+1)^A 2^{16n}` of the archimedean bound (L4). -/
def archBound (Cst : ℝ) (A n : ℕ) : ℝ :=
  Cst * ((n : ℝ) + 1) ^ A * (2 : ℝ) ^ (16 * n)

/-! ## 2-adic Δ-calculus (proof.md P3; Lai Def. 2.3) -/

/-- Lai's `Δ_m(f) ≥ c`: for every `k ≥ 2^m`, `v₂(f(k) - f(k₋)) ≥ c + v₂(k - k₋)`, where
`k₋ = k - 2^{⌊log₂ k⌋}` is `k` with its leading binary digit removed (so `k - k₋ = 2^{⌊log₂ k⌋}`). -/
def DeltaGe (m : ℕ) (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k : ℕ, 2 ^ m ≤ k →
    ‖f k - f (k - 2 ^ Nat.log 2 k)‖ ≤ (2 : ℝ) ^ (-(c + (Nat.log 2 k : ℤ)))

/-- Lai's `Δ(f) ≥ c`: `Δ₀(f) ≥ c` and `v₂(f 0) ≥ c - 1`. -/
def DeltaAll (c : ℤ) (f : ℕ → ℚ_[2]) : Prop :=
  DeltaGe 0 c f ∧ ‖f 0‖ ≤ (2 : ℝ) ^ (1 - c)

/-- `f` takes values in `ℤ₂`. -/
def IntValued (f : ℕ → ℚ_[2]) : Prop :=
  ∀ k, ‖f k‖ ≤ 1

/-! ## Objects of the nonvanishing lemma L5 (proof.md §7) -/

/-- `C(x+n, n)`. -/
def Bn (n x : ℕ) : ℕ := Nat.choose (x + n) n

/-- `Y_l(x) = C(x+l-1, l-1) C(x+n, n-l)`, so that `(x+1)_n / (x+l) = (l-1)! (n-l)! Y_l(x)`. -/
def Yl (n l x : ℕ) : ℕ := Nat.choose (x + l - 1) (l - 1) * Nat.choose (x + n) (n - l)

/-- `(l-1)! (n-l)!`. -/
def Wl (n l : ℕ) : ℕ := (l - 1).factorial * (n - l).factorial

/-- `h_β(x) = [δ^β] ∏_{k=0}^{n} (2x+2k+1+δ)^{-8}`, i.e. `h^{(β)}(x) / (β! 2^β)` for
`h(t) = ∏_{k=0}^{n} (2t+2k+1)^{-8}`. -/
def hcoef (n β x : ℕ) : ℚ :=
  coeff β (∏ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 8)⁻¹)

/-- One Leibniz term of `integrand n x = -6 · 2^{24n+8} [ε^3] ((2x+1+n+2ε) P(x+ε)^8 h(x+ε))`,
`P(t) = (t+1)_n`: `γ` derivatives on the linear factor, `β` on `h`, and the multiplicity function
`M` (support in `[1,n]`, total `a = 3-γ-β`) on the factors `(x+l)^8` of `P^8`.  Uses
`∏_l (x+l)^{8-M l} = n!^{8-a} C(x+n,n)^{8-a} ∏_l ((l-1)!(n-l)! Y_l(x))^{M l}`. -/
def leibTerm (n γ β : ℕ) (M : ℕ →₀ ℕ) (x : ℕ) : ℚ :=
  -6 * (2 : ℚ) ^ (24 * n + 8) * (if γ = 0 then ((2 * x + 1 + n : ℕ) : ℚ) else 2) * (2 : ℚ) ^ β *
    hcoef n β x * (∏ l ∈ Icc 1 n, ((Nat.choose 8 (M l) : ℕ) : ℚ)) *
    ((n.factorial : ℕ) : ℚ) ^ (5 + γ + β) * ((Bn n x : ℕ) : ℚ) ^ (5 + γ + β) *
    ∏ l ∈ Icc 1 n, (((Wl n l : ℕ) : ℚ) * ((Yl n l x : ℕ) : ℚ)) ^ (M l)

/-- The dominant Leibniz term for `n = 2^m - 1`, `k₀ = 2^{m-1}` (γ = 1, β = 0, M = {k₀,k₀}):
`-336 · 2^{24n+8} n!^6 ((k₀-1)!(n-k₀)!)^2 C(x+n,n)^6 Y_{k₀}(x)^2 h_0(x)`. -/
def domTerm (m x : ℕ) : ℚ :=
  -336 * (2 : ℚ) ^ (24 * (2 ^ m - 1) + 8) * (((2 ^ m - 1).factorial : ℕ) : ℚ) ^ 6 *
    ((Wl (2 ^ m - 1) (2 ^ (m - 1)) : ℕ) : ℚ) ^ 2 * ((Bn (2 ^ m - 1) x : ℕ) : ℚ) ^ 6 *
    ((Yl (2 ^ m - 1) (2 ^ (m - 1)) x : ℕ) : ℚ) ^ 2 * hcoef (2 ^ m - 1) 0 x

/-- The exact 2-adic valuation of `S_{2^m-1}` (proof.md L5): `32 n + 14 - 11 m`, `n = 2^m - 1`. -/
def target (m : ℕ) : ℤ :=
  32 * ((2 : ℤ) ^ m - 1) + 14 - 11 * (m : ℤ)

/-! ## Basic API (proved here, available to every proof file) -/

theorem volkenbornSum_add (f g : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => f x + g x) N = volkenbornSum f N + volkenbornSum g N := by
  unfold volkenbornSum
  rw [Finset.sum_add_distrib, mul_add]

theorem volkenbornSum_const_mul (a : ℚ_[2]) (f : ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => a * f x) N = a * volkenbornSum f N := by
  unfold volkenbornSum
  rw [← Finset.mul_sum]
  ring

theorem volkenbornSum_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ_[2]) (N : ℕ) :
    volkenbornSum (fun x => ∑ i ∈ s, F i x) N = ∑ i ∈ s, volkenbornSum (F i) N := by
  unfold volkenbornSum
  rw [Finset.sum_comm, Finset.mul_sum]

theorem HasVolkenborn.add {f g : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (hf : HasVolkenborn f I)
    (hg : HasVolkenborn g I') : HasVolkenborn (fun x => f x + g x) (I + I') := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => f x + g x) = fun N => volkenbornSum f N + volkenbornSum g N
    from funext (volkenbornSum_add f g)]
  exact hf.add hg

theorem HasVolkenborn.const_mul {f : ℕ → ℚ_[2]} {I : ℚ_[2]} (a : ℚ_[2]) (hf : HasVolkenborn f I) :
    HasVolkenborn (fun x => a * f x) (a * I) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => a * f x) = fun N => a * volkenbornSum f N
    from funext (volkenbornSum_const_mul a f)]
  exact hf.const_mul a

theorem HasVolkenborn.sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → ℚ_[2]} {I : ι → ℚ_[2]}
    (h : ∀ i ∈ s, HasVolkenborn (F i) (I i)) :
    HasVolkenborn (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, I i) := by
  unfold HasVolkenborn at *
  rw [show volkenbornSum (fun x => ∑ i ∈ s, F i x) = fun N => ∑ i ∈ s, volkenbornSum (F i) N
    from funext (volkenbornSum_sum s F)]
  exact tendsto_finsetSum s h

theorem HasVolkenborn.unique {f : ℕ → ℚ_[2]} {I I' : ℚ_[2]} (h : HasVolkenborn f I)
    (h' : HasVolkenborn f I') : I = I' :=
  tendsto_nhds_unique h h'

theorem HasVolkenborn.volkenborn_eq {f : ℕ → ℚ_[2]} {I : ℚ_[2]} (h : HasVolkenborn f I) :
    volkenborn f = I :=
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨I, h⟩) h

/-- The rational `(x + 1/2)^{-s}` maps to `halfPow s x`. -/
theorem halfPow_eq_cast (s x : ℕ) :
    halfPow s x = (((((x : ℚ) + 1 / 2)⁻¹) ^ s : ℚ) : ℚ_[2]) := by
  simp [halfPow, one_div]

/-- Membership in `chains m N`: values `≤ N` and monotone. -/
theorem mem_chains {m N : ℕ} {i : Fin m → ℕ} :
    i ∈ chains m N ↔ (∀ k, i k ≤ N) ∧ ∀ a b : Fin m, a ≤ b → i a ≤ i b := by
  simp [chains, Fintype.mem_piFinset]

/-- Along a chain, `i_{k-1} ≤ i_k` (so `i k - chainPrev i k` is an honest difference). -/
theorem chainPrev_le {m N : ℕ} {i : Fin m → ℕ} (hi : i ∈ chains m N) (k : Fin m) :
    chainPrev i k ≤ i k := by
  unfold chainPrev
  split_ifs with h
  · exact Nat.zero_le _
  · exact (mem_chains.1 hi).2 _ _ (by rw [Fin.le_def]; simp)

/-- `Φ_n ∣ d_n`: `Φ_n` is a product of distinct primes `≤ n`. -/
theorem Phi_dvd_dn (n : ℕ) : Phi n ∣ dn n := by
  have h1 : Phi n ∣ primorial n := by
    unfold Phi primorial
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  exact h1.trans (Nat.primorial_dvd_lcmUpto n)

theorem Phi_pos (n : ℕ) : 0 < Phi n := by
  unfold Phi
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact hp.2.1.pos

theorem Dn_pos (n : ℕ) : 0 < Dn n := by
  unfold Dn
  have hd : 0 < dn n := Nat.lcmUpto_pos n
  have hdvd : Phi n ∣ dn n ^ 12 := (Phi_dvd_dn n).trans (dvd_pow_self _ (by norm_num))
  exact Nat.div_pos (Nat.le_of_dvd (pow_pos hd 12) hdvd) (Phi_pos n)

/-- `D_n · Φ_n = d_n^{12}`. -/
theorem Dn_mul_Phi (n : ℕ) : Dn n * Phi n = dn n ^ 12 := by
  unfold Dn
  exact Nat.div_mul_cancel ((Phi_dvd_dn n).trans (dvd_pow_self _ (by norm_num)))

end Zeta2

end
