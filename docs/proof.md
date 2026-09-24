# At least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational — proof draft

Track 1 (prove-7-9-11), 2026-09-24. Raw working document for another model. Every lemma is marked
**PROVED** (complete argument given here, modulo cited published lemmas),
**PROVED + NUMERICAL** (complete argument, and additionally checked on exact data),
**SKETCH** or **NUMERICAL** (evidence only).

---------------------------------------------------------------------------------------------------

## 0. Statement and status

**Theorem.** Let ζ₂ be the Kubota–Leopoldt 2-adic zeta function, ζ₂(s) := L₂(s, ω^{1−s}) (so ζ₂(even) = 0).
At least one of the three 2-adic numbers ζ₂(7), ζ₂(9), ζ₂(11) is irrational.

This sharpens L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235
(arXiv:2304.00816), Thm 1.1 with s = 3 ("at least one of ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13) is irrational"):
ζ₂(13) is removed.

| step | content | status |
|---|---|---|
| L1 | S_n = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9) + Z₁₁ζ₂(11), rational coefficients; ζ₂(5)-coefficient and all even values vanish | **PROVED + NUMERICAL** (n ≤ 300, 383, 447, 511) |
| L2a | d_n^{8−i} r_{i,k} ∈ ℤ, hence d_n^{8−i} Z_i ∈ ℤ | **PROVED** (standard) |
| L2b | d_n^{12} ρ₀ ∈ ℤ (all primes, incl. 2) | **PROVED** (root trick, Lai Lemma 4.6 style) |
| L2c | v_p(ρ₀) ≥ −11 for every prime p ≥ 11 with p² > 2n (the "one-power saving") | **PROVED** (Andrews transformation, LSZ Lemma 5.3 generalised) **+ NUMERICAL** |
| L2 cor | D_n := d_n^{12}/Φ_n, Φ_n := ∏_{max(√(2n),10) < p ≤ n} p, clears all denominators; log D_n = 11n + o(n) | **PROVED** (PNT) |
| L3 | v₂(S_n) ≥ 32n + 5 − 12 log₂(n+1) for all n ≥ 1 | **PROVED + NUMERICAL** (not needed for the theorem) |
| L4 | |r_{i,k}| ≤ 4^{8−i}(n+½)2^{16n}; max(|ρ₀|,|Z_i|) ≤ 3.4·10⁸ (n+1)² 2^{16n} | **PROVED + NUMERICAL** |
| L5 | for n = 2^m − 1 (m ≥ 2): v₂(S_n) = 32n + 14 − 11m exactly; in particular S_n ≠ 0 | **PROVED + NUMERICAL** (m = 2..9 exact, two independent codes) |
| L6 | conclusion via Lai's criterion along n = 2^m − 1; exponent 11 − 16 log 2 = −0.09035 | **PROVED** (given L1–L5) |

Honest caveats: (i) the whole proof is new and has not been refereed; the risky steps (L2c, L5) are
each backed by exact computer checks listed in §9, but a human referee should re-derive them.
(ii) The margin is thin (−0.0904 per n) but it is an honest asymptotic exponent; nothing below depends on
numerics. (iii) Novelty: a quick web search (2026-09-24) found no prior statement of the {7,9,11} result;
not exhaustive.

---------------------------------------------------------------------------------------------------

## 1. How the literature proves each ingredient (extraction)

* **Lai 2304.00816** (the {7,9,11,13} theorem). Rational function
  A_n(t) = 2^{(6s+12)n}(4t+2n)^δ (t+¼)_n^{s+2}(t+¾)_n^{s+2}/(t)_{n+1}^{2s+4}; S_n = ∫_{ℤ₂} A_n^{(s)}(t+¼)dt.
  - linear form: partial fractions + translation lemma + ∫(t+¼)^{−j} = j4^j ζ₂(j+1,¼); ρ_{n,1}=0 by degree,
    parity from A_n(−t−n) = (−1)^δ A_n(t) (Lemma 3.3).
  - denominators: d_n^{2s+4−i} a_{n,i,k} ∈ ℤ (Leibniz + building blocks, Lemma 4.2); prime-selective saving
    Φ_n = ∏_{√(10n)<q≤n, {n/q}>½} q from explicit factorial ratios (Lemma 4.3, needs n odd);
    ρ_{n,0}: d_n^{3s+5} by the "root trick" (Lemma 4.6: t = −k₀+ℓ₀+¼ is a multiple root, so each term can be
    rewritten; a q-adic contradiction v_q(k₁−k₀) > v_q(d_n)). **Lai uses d_n^{a+j+1} (no one-power saving)**
    and compensates with Φ_n^{s+2}.
  - 2-adic smallness: Sprang's operator Δ, Δ_m (Def. 2.3), v_p(∫f) ≥ Δ(f)−1 and the Riemann-sum congruence
    ∫f ≡ p^{−m}Σ_{k<p^m} f(k) mod p^{Δ_m(f)−1} (Lemma 2.4); Δ of products/binomials (Lemma 2.5).
  - archimedean: Cauchy integral for a_{n,i,k} (Lemma 5.2).
  - **nonvanishing** (the hard step): only along n = 2^m − 1. Leibniz-expand A_n^{(s)}(t+¼); by Lemma 6.1
    (binary digit sums: v₂((k−1)!(n−k)!) is uniquely minimal at k₀ = 2^{m−1}) the term with all s
    derivatives on (t+k₀)^{s+2} dominates; its integral is computed exactly by the Riemann sum at level m
    (only x = 0 survives mod 2 since C(x+2^m−1, 2^m−1) is even for 1 ≤ x < 2^m), all other terms are bounded
    by Δ-calculus (Lemma 6.2).
  - conclusion: elementary criterion Lemma 2.1.
* **Lai–Sprang–Zudilin 2505.05005** (ζ₂(5), μ ≤ 20.342). R_n(t) = 2^{8n}(2t+n)(t+½)_n^4/(t)_{n+1}^4,
  S_n = −∫R_n'(t+½)dt (our family with (a,j) = (4,1)).
  - linear form Lemma 3.3 (identical mechanism to our L1).
  - denominators: standard gives d_n ρ_{n,3}, d_n^6 ρ_{n,0} (Lemma 5.1) = d_n^{a+j+1}; the one-power saving
    v_p(ρ_{n,0}) ≥ −5 for p > max(√(2n),3) (Lemma 5.3) via **Andrews' multiple-sum transformation of a
    terminating very-well-poised ₁₃V₁₂** (Krattenthaler–Rivoal Thm 8) and a 5-case binomial divisibility
    argument, then Zudilin's derivative lemma; Φ_n = ∏_{max(√(2n),3)<p≤n} p (Lemma 5.4). ρ_{n,3} ∈ ℤ (Lemma 5.2).
  - 2-adic: Δ-calculus with Leibniz on 2^{12n+4} g(t)∏(t+j)^4 (Lemma 6.2): v₂ ≥ 16n+3−6log₂(n+1).
  - archimedean + nonvanishing: a three-term Apéry-like recursion (Zeilberger certificate, Lemma 4.1) gives
    Poincaré asymptotics and a Casoratian ρ_{n,0}ρ_{n+1,3} − ρ_{n+1,0}ρ_{n,3} = 3·2^{16n+18}/(n+1)^5 ≠ 0;
    Bel's lemma (two consecutive forms cannot both vanish). This only works for a single zeta value.
* **Lai–Lupu–Sprang 2505.23088** (p ≥ 5 Zudilin analogue). Denominators with a floor-function Φ_n
  (Lemma 5.4) and root trick (Lemma 5.6); nonvanishing along a special subsequence n(N) by computing the exact
  p-adic valuation of the boundary term Σ_j R̃_n(j/p) (primitive, Laurent expansion at ∞) which dominates
  the Bernoulli-functional part (Lemmas 6.1–6.3).
* **Beukers, math/0603277** (Acta Math. Sin. 2008): Padé approximants to p-adic Hurwitz-type functions;
  nonvanishing from the Casoratian p_{n+1}q_n − p_n q_{n+1} = 1/(n+1)² of the Apéry recurrence.
* **Calegari 2005** (IMRN): ζ₂(3), ζ₃(3) via overconvergent p-adic modular forms and Apéry-type recurrences
  (not re-read here; from secondary descriptions in LSZ/Lai).
* **Lai–Sprang 2306.10393**: replaces nonvanishing by an ℓ(n)-adic condition on the coefficients
  (Lemma 2.2: if v_{ℓ(n)}(l_{0,n}) < v_{ℓ(n)}(l_{i,n}) for i ≥ 1 with ℓ(n) → ∞, the forms are eventually
  nonzero). Mentioned in §11 as an alternative route.

What we adopt: LSZ's family generalised to (a,j) = (8,3); LSZ's Andrews argument for the one-power denominator
saving (it generalises verbatim, §4.3); Lai's dominant-term method for nonvanishing on n = 2^m − 1, with one
new twist (§7: the factor (2t+n+1) vanishes exactly at the dominant point and is handled by the identity
(t+2^{m−1})·C(t+n,n) = 2^{m−1}[C(t+n,n) + 2C(t+n,n+1)]).

---------------------------------------------------------------------------------------------------

## 2. Notation and tools

d_n = lcm(1,…,n); ψ, θ Chebyshev functions; (x)_k rising factorial; C(x,k) binomial; s₂(a) binary digit sum,
v₂(a!) = a − s₂(a); D_λ := (1/λ!)(d/dt)^λ. For f: ℤ₂ → ℚ₂ and k ≥ 1, k₋ := k minus its leading binary digit.

(P1) **Volkenborn integral** ∫_{ℤ₂} f(t)dt := lim_N 2^{−N}Σ_{x<2^N} f(x); exists for strictly differentiable f,
in particular for rational functions without poles in ℤ₂ [Robert, Ch. 5]. **Translation**: for k ≥ 1,
∫f(t+k)dt = ∫f(t)dt + Σ_{ℓ=0}^{k−1} f'(ℓ) [Robert §5.3 Prop. 2; LSZ Lemma 2.4; Lai Lemma 2.2].

(P2) **2-adic zeta values** [LSZ Lemma 2.8 + §2.3]: for s ≥ 1, J_s := ∫_{ℤ₂}(t+½)^{−s}dt = s·2^{s+1}·ζ₂(s+1);
ζ₂(2k) = 0, hence J_s = 0 for odd s.

(P3) **Δ-calculus** [Lai Def. 2.3, Lemmas 2.4, 2.5; LSZ Lemmas 2.5, 2.6]:
Δ_m(f) := inf_{k≥2^m} v₂((f(k)−f(k₋))/(k−k₋)), Δ(f) := min{1+v₂(f(0)), Δ₀(f)}.
 (a) v₂(∫f) ≥ Δ(f) − 1, and ∫f ≡ 2^{−m}Σ_{k<2^m} f(k) (mod 2^{Δ_m(f)−1}ℤ₂).
 (b) Δ(f+g) ≥ min(Δf, Δg); Δ(Cf) = Δ(f) + v₂(C).
 (c) f, g ∈ S¹(ℤ₂,ℤ₂) (ℤ₂-valued): Δ(fg) ≥ min(Δf, Δg), Δ_m(fg) ≥ min(Δ_m f, Δ_m g).
 (d) f = Σ a_j t^j ∈ ℤ₂[[t]] with a_j → 0: Δ_m(f) ≥ Δ(f) ≥ 0.
 (e) f = C(t+x, N), x ∈ ℤ, N ≥ 1: Δ_m(f) ≥ Δ(f) ≥ −⌊log₂ N⌋; and for m > ⌊log₂ N⌋: Δ_m(f²) ≥ 1 − ⌊log₂ N⌋.

(P4) **Criterion** [Lai Lemma 2.1]: α₁..α_s ∈ ℚ_p; integers a_{n,0..s}; if max_i|a_{n,i}|·|a_{n,0}+Σa_{n,i}α_i|_p → 0
along an unbounded set of n on which a_{n,0}+Σ a_{n,i}α_i ≠ 0, then some α_i is irrational.

(P5) **Building blocks** [Lai–Yu Compos. 2020 Lemma 4.2 = LLS Lemma 5.2 with (a,b) = (1,2); Zudilin JTNB 2004
Lemma 16]: F(t) := 2^{2n}(t+½)_n/n! satisfies d_n^λ D_λF(t)|_{t=−k} ∈ ℤ for all k ∈ ℤ, λ ≥ 0;
G(t) := n!/(t)_{n+1} satisfies d_n^λ D_λ((t+k)G(t))|_{t=−k} ∈ ℤ for 0 ≤ k ≤ n.

(P6) **Andrews' transformation** [Andrews 1975 Thm 4, q→1; Krattenthaler–Rivoal, Mem. AMS 186 (2007) no. 875,
Théorème 8, checked verbatim in arXiv math/0311114 p. 17]: for integers m, N ≥ 0,
```
2m+5F2m+4[ a, a/2+1, b1, c1, ..., b_{m+1}, c_{m+1}, -N ;  a/2, 1+a-b1, 1+a-c1, ..., 1+a-b_{m+1}, 1+a-c_{m+1}, 1+a+N ; 1 ]
 = (1+a)_N (1+a-b_{m+1}-c_{m+1})_N / ((1+a-b_{m+1})_N (1+a-c_{m+1})_N)
   * sum_{0<=i_1<=...<=i_m<=N}  (-N)_{i_m}/(b_{m+1}+c_{m+1}-a-N)_{i_m}
     * prod_{k=1}^m (1+a-b_k-c_k)_{i_k-i_{k-1}} (b_{k+1})_{i_k} (c_{k+1})_{i_k} / ((i_k-i_{k-1})! (1+a-b_k)_{i_k} (1+a-c_k)_{i_k})
```
(i₀ = 0), an identity of rational functions of the parameters.

(P7) **Lai's digit lemma** [Lai Lemma 6.1]: n = 2^m−1 (m ≥ 2), k₀ = 2^{m−1}: for 1 ≤ k ≤ n,
W_k := v₂((k−1)!(n−k)!) satisfies W_{k₀} = n+1−2m and W_k ≥ n+2−2m for k ≠ k₀.

(P8) PNT: ψ(x) = x + o(x), θ(x) = x + o(x), ψ(x) − θ(x) = O(√x).

---------------------------------------------------------------------------------------------------

## 3. The construction and L1 (linear form) — **PROVED + NUMERICAL**

For n ≥ 0 let
  R_n(t) := 2^{16n}(2t+n)(t+½)_n^8/(t)_{n+1}^8,   deg R_n = −7,
  S_n := −∫_{ℤ₂} R_n'''(t+½) dt ∈ ℚ₂.
R_n(t+½) has no pole in ℤ₂ (poles at −½−k have |·|₂ = 2), so S_n is defined. Partial fractions:
R_n(t) = Σ_{i=1}^{8}Σ_{k=0}^{n} r_{i,k}(t+k)^{−i}, c_i := Σ_k r_{i,k}.

**Lemma 1.** S_n = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9) + Z₁₁ζ₂(11) with
  Z_{i+4} := (i)₄·2^{i+4}·c_i  (i = 3,5,7; i.e. Z₇ = 46080c₃, Z₉ = 860160c₅, Z₁₁ = 10321920c₇),
  ρ₀ := −Σ_{i=1}^{8}Σ_{k=1}^{n} (i)₄ r_{i,k} A_k^{(i+4)},  A_k^{(s)} := Σ_{ℓ=0}^{k−1}(ℓ+½)^{−s} = Σ_{ℓ=1}^{k}(ℓ−½)^{−s}.

*Proof.* R_n''' = −Σ(i)₃ r_{i,k}(t+k)^{−i−3}, so S_n = Σ_{i,k}(i)₃ r_{i,k}∫(t+k+½)^{−i−3}dt. By (P1) with
f(t) = (t+½)^{−i−3}: ∫(t+k+½)^{−i−3} = J_{i+3} − (i+3)A_k^{(i+4)}. By (P2) J_{i+3} = (i+3)2^{i+4}ζ₂(i+4).
Hence S_n = ρ₀ + Σ_{i=1}^{8}(i)₄2^{i+4}c_iζ₂(i+4). Now: c₁ = lim_{t→∞} tR_n(t) = 0 (deg ≤ −2) — this kills
ζ₂(5); for even i, ζ₂(i+4) = 0 (P2) (and independently c_i = 0 for even i because R_n(−t−n) = −R_n(t)
gives r_{i,n−k} = (−1)^{i+1}r_{i,k}). Remaining i = 3,5,7. ∎

Exact data: for all n ≤ 300 and n ∈ {383, 447, 511}: c₁ = 0, c_even = 0, only ζ₂(7), ζ₂(9), ζ₂(11) occur
(ledger83.jsonl). Small cases: n=0: S₀ = 20643840ζ₂(11); n=1: ρ₀ = 14155776, Z = (−849346560,
21139292160, 52848230400); (a,j) = (4,1) specialisation reproduces LSZ exactly (ρ_{1,0} = −1024,
ρ_{1,3} = 73728, their recursion (1.1) for n ≤ 11).

Useful formula (verified): for 0 ≤ k ≤ n,
  G_k(ε) := ε^8R_n(−k+ε) = 2^{16n}(n−2k+2ε)·Ψ_k(ε)^8,  Ψ_k(ε) := (½−ε)_k(½+ε)_{n−k}/((1−ε)_k(1+ε)_{n−k}),
  r_{8−μ,k} = [ε^μ]G_k(ε),  G_k(0) = (n−2k)·(C(2k,k)C(2n−2k,n−k))^8 ∈ ℤ.

---------------------------------------------------------------------------------------------------

## 4. L2 — denominators

### 4.1 L2a: d_n^{8−i}r_{i,k} ∈ ℤ — **PROVED** (standard)
(t+k)^8R_n(t) = (2t+n)·F(t)^8·((t+k)G(t))^8 with F, G of (P5) (indeed F^8G^8 = 2^{16n}(t+½)_n^8/(t)_{n+1}^8).
r_{i,k} = D_{8−i}((t+k)^8R_n)|_{t=−k}; expand by Leibniz; each factor d_n^λD_λ(·)|_{−k} is an integer by (P5).
Hence d_n^{8−i}r_{i,k} ∈ ℤ (including the prime 2), d_n^{8−i}c_i ∈ ℤ, d_n^{8−i}Z_{i+4} ∈ ℤ.
(Numerically the Z's are one power better: d_n⁴Z₇, d_n²Z₉, Z₁₁ ∈ ℤ for all tested n — not needed.)

### 4.2 L2b: d_n^{12}ρ₀ ∈ ℤ — **PROVED** (root trick; Lai Lemma 4.6 / LLS Lemma 5.6)
Write ρ₀ = −Σ_{k=1}^{n}Σ_{ℓ₀=0}^{k−1} X(k,ℓ₀), X(k,ℓ₀) := Σ_i (i)₄ r_{i,k}(ℓ₀+½)^{−(i+4)}.
2-adically every term is fine (2 ∤ 2ℓ₀+1, and L2a). Suppose d_n^{12}X(k₀,ℓ₀) ∉ ℤ_(q) for an odd prime q.
Then some i₀ has v_q(d_n^{12}r_{i₀,k₀}(ℓ₀+½)^{−i₀−4}) < 0, so by L2a v_q(2ℓ₀+1) > v_q(d_n).
The point t₀ := −k₀+ℓ₀+½ satisfies t₀+½+(k₀−ℓ₀−1) = 0 with 0 ≤ k₀−ℓ₀−1 ≤ n−1, so it is a zero of R_n of
order 8 > 4, hence R_n^{(4)}(t₀) = Σ_{i,k}(i)₄r_{i,k}(t₀+k)^{−i−4} = 0, i.e.
X(k₀,ℓ₀) = −Σ_{k≠k₀}Σ_i(i)₄r_{i,k}(ℓ₀−k₀+k+½)^{−i−4}. So some k₁ ≠ k₀ has v_q(2(ℓ₀−k₀+k₁)+1) > v_q(d_n).
Subtracting: q^{v_q(d_n)+1} | 2(k₁−k₀), impossible as 0 < |k₁−k₀| ≤ n. Hence d_n^{12}ρ₀ ∈ ℤ.
(Primes n < q < 2n therefore never occur in the denominator.)

### 4.3 L2c: v_p(ρ₀) ≥ −11 for primes p ≥ 11 with p² > 2n — **PROVED + NUMERICAL**
This is the (8,3) analogue of LSZ Lemma 5.3; the proof generalises verbatim.

**Step 1 (residue form).** Since (j+1)!/(x−ε)^{j+2} = Σ_{i≥1}(i)_{j+1}x^{−(i+j+1)}ε^{i−1}, with j = 3:
Σ_i(i)₄r_{i,k}x^{−(i+4)} = 24·Res_{ε=0} R_n(−k+ε)(x−ε)^{−5}. Using ℓ = ℓ₀+1 ∈ [1,k] and
(½−ε)_k = (½−ε)_{ℓ−1}(ℓ−½−ε)(ℓ+½−ε)_{k−ℓ} (k ≥ ℓ), the factor (ℓ−½−ε)^{−5} is absorbed:
  ρ₀ = −24 Σ_{ℓ=1}^{n} [ε^7] T_{n,ℓ}(ε),
  T_{n,ℓ}(ε) := 2^{16n}(ℓ−½−ε)^3(½−ε)_{ℓ−1}^8 Σ_{k=ℓ}^{n}(n−2k+2ε)(ℓ+½−ε)_{k−ℓ}^8(½+ε)_{n−k}^8 / ((1−ε)_k^8(1+ε)_{n−k}^8).
(Verified exactly for n ∈ {1,…,7,9}: andrews_check.py (2).)

**Step 2 (VWP form).** Put N := n−ℓ, k = ℓ+κ, a := −n+2ℓ−2ε, b := −N−ε, c := ℓ+½−ε. Then
1+a−b = ℓ+1−ε, 1+a−c = ½−ε−N, n−2k+2ε = −(a+2κ), and with (x)_{N−κ} = (−1)^κ(x)_N/(1−x−N)_κ:
  T_{n,ℓ}(ε) = −a·P_ℓ(ε)·Σ_{κ=0}^{N} ((a+2κ)/a)·[(b)_κ(c)_κ/((1+a−b)_κ(1+a−c)_κ)]^8,
  P_ℓ(ε) := 2^{16n}(ℓ−½−ε)^3(½−ε)_{ℓ−1}^8(½+ε)_N^8/((1−ε)_ℓ^8(1+ε)_N^8).
The κ-sum equals lim_{δ→0} of the ₂₁F₂₀ of (P6) with m = 8, (b_k,c_k) = (b,c) for k ≤ 8, (b₉,c₉) = (1, ℓ+1−2ε−δ),
and −N: the pair (1,c₉) supplies κ!(c₉)_κ/((a)_κ(−N+δ)_κ), cancelling (a)_κ/κ!, and
(c₉)_κ(−N)_κ/((−N+δ)_κ(1+a+N)_κ) → 1 for κ ≤ N (and = 0 for κ > N) since 1+a+N = ℓ+1−2ε. All limits on the
right side of (P6) are regular at δ = 0: (1+a−c₉)_N = (−N+δ)_N → (−N)_N ≠ 0, b₉+c₉−a−N = 2−δ.

**Step 3 (Andrews).** With 1+a−b−c = ½, (P6) gives, writing J_i := i_i, d_i := J_i − J_{i−1}:
  T_{n,ℓ}(ε) = Σ_{0≤J₁≤…≤J₈≤N} F_J(ε),
  F_J(ε) = −(N+1)(ℓ−2ε)P_ℓ(ε) ∏_{i=1}^{8}(½)_{d_i}/d_i! ∏_{i=1}^{7}(−N−ε)_{J_i}(ℓ+½−ε)_{J_i}/((ℓ+1−ε)_{J_i}(½−ε−N)_{J_i})
           · (ℓ+1−2ε)_{J₈}(−N)_{J₈}/((J₈+1)(ℓ+1−ε)_{J₈}(½−ε−N)_{J₈}).
(Prefactor: (1+a)_N(a−c₉)_N/((a)_N(1+a−c₉)_N) → (N+1)(a+N)/a, a+N = ℓ−2ε.)
Verified as an exact rational identity at random rational ε for all 1 ≤ ℓ ≤ n ≤ 8 (andrews_check.py (1),
extra_checks.py (i)).

**Step 4 (value at ε = 0).** Using (½)_m/m! = C(2m,m)4^{−m}, (½)_{ℓ−1}/ℓ! = C(2ℓ−2,ℓ−1)/(4^{ℓ−1}ℓ),
(−N)_J(ℓ+½)_J/((ℓ+1)_J(½−N)_J) = C(2(ℓ+J),ℓ+J)C(2(N−J),N−J)/(C(2ℓ,ℓ)C(2N,N)), and
(−N)_J/((J+1)(½−N)_J) = 4^J C(2(N−J),N−J)/((J+1)C(2N,N)), all powers of 2 collapse and
  F_J(0) = −64·(2ℓ−1)^{−4}·C(2ℓ−2,ℓ−1)·(N+1)/(J₈+1)·∏_{i=1}^{8}C(2d_i,d_i)·∏_{i=1}^{7}C(2(ℓ+J_i),ℓ+J_i)·∏_{i=1}^{8}C(2(N−J_i),N−J_i).
(For (a,j) = (4,1) the same computation reproduces LSZ's displayed F exactly; for (8,3) verified against the
Pochhammer form for all chains, n ≤ 7: andrews_check.py (3).)

**Step 5 (p-adic valuation of F_J(0)).** Let p ≥ 11, p² > 2n. All integers ≤ 2n have v_p ≤ 1.
Trivially v_p(F_J(0)) ≥ −4v_p(2ℓ−1) − v_p(J₈+1) ≥ −5. Claim: v_p(F_J(0)) ≥ −4. We use
(⋆) p | C(2m,m) whenever (m mod p) ≥ (p+1)/2 (a carry in m+m, Kummer).
Assume p | 2ℓ−1 and p | J₈+1, i.e. ℓ ≡ (p+1)/2, J₈ ≡ −1 (mod p). Let x := J₁ mod p.
 - x ≥ (p+1)/2: p | C(2J₁,J₁) = C(2d₁,d₁).
 - x ≤ (p−3)/2: (ℓ+J₁) mod p ∈ [(p+1)/2, p−1], so p | C(2(ℓ+J₁),ℓ+J₁).
 - x = (p−1)/2: then N−J₁ ≡ n (mod p). If (n mod p) ≥ (p+1)/2: p | C(2(N−J₁),N−J₁). If (n mod p) = (p−1)/2:
   N+1 = n−ℓ+1 ≡ 0. If (n mod p) ≤ (p−3)/2: N−J₈ ≡ n+(p+1)/2 has residue in [(p+1)/2, p−1], so
   p | C(2(N−J₈),N−J₈).
All the factors used are present in F_J(0). Hence v_p(F_J(0)) ≥ −4 in all cases (sharp; the value −4 occurs).
Checked on 200000 random chains biased to the critical case (n ≤ 400): andrews_check.py (4).

**Step 6 (derivatives; Zudilin 2004 Lemma 17 style).** F_J(ε)/F_J(0) = ∏_s(1+ε/α_s)^{e_s} over the linear
factors listed in Step 3 (e.g. ℓ−½−ε, r+½±ε, r±ε, ℓ−2ε = ℓ(1−2ε/ℓ), −N+r−ε, ℓ+1+r−2ε, ½−N+r−ε), with
2α_s ∈ ℤ∖{0}, |2α_s| ≤ 2n, so v_p(α_s) ≤ 1; none vanishes at ε = 0. Hence log(F_J(ε)/F_J(0)) = ΣL_με^μ with
L_μ = Σ_s e_s(−1)^{μ−1}/(μα_s^μ), v_p(L_μ) ≥ −μ for μ < p, and [ε^7] of the exponential has v_p ≥ −7
(the 1/k! with k ≤ 7 < p are units). Thus v_p([ε^7]F_J) ≥ −4−7 = −11, so v_p([ε^7]T_{n,ℓ}) ≥ −11 for every ℓ
and v_p(ρ₀) ≥ −11 (24 is a p-unit). ∎
Per-ℓ check (stronger than needed), exact: v_p([ε^7]T_{n,ℓ}) ≥ −11 for n ∈ {18,22,26,30}, all ℓ, all such p;
the bound −11 is attained (perell_check.out).

### 4.4 Corollary (common denominator) — **PROVED**
Φ_n := ∏_{p prime, max(√(2n),10) < p ≤ n} p, D_n := d_n^{12}/Φ_n. Then
D_nρ₀, D_nZ₇, D_nZ₉, D_nZ₁₁ ∈ ℤ.
(For p | Φ_n: v_p(d_n) = 1, so v_p(d_n^{12}ρ₀) ≥ 12−11 = 1 by L2c; other primes by L2b. For Z: L2a and
Φ_n | d_n.) Moreover log D_n = 12ψ(n) − θ(n) + θ(max(√(2n),10)) = 11n + o(n) by (P8).
Exact data (n ≤ 300, 383, 447, 511): the odd part of the true common denominator always divides d_n^{11};
the 2-part of the true common denominator is 1 except at n ∈ {32,64,128,256,257,258,260,264,272,288}
(exponents 1,5,9,13,4,4,4,4,4,4 — well inside the 2^{12v₂(d_n)} allowed by L2a/L2b), and it is 1 for all
n = 2^m−1; ρ₀ genuinely needs d_n^{11} (odd-part exponent 11 for 298 of 303 n; the exceptions are n ≤ 6).

---------------------------------------------------------------------------------------------------

## 5. L3 — 2-adic smallness for all n — **PROVED + NUMERICAL** (not needed for the theorem)

R_n(t+½) = 2^{24n+8}g(t)P(t)^8 with P(t) := (t+1)_n = ∏_{l=1}^n(t+l), g(t) := (2t+1+n)∏_{k=0}^n(2t+2k+1)^{−8} ∈ ℤ₂[[2t]]
(because (t+½)_{n+1} = 2^{−n−1}∏(2t+2k+1)). Leibniz over the 8n linear factors and g:
(gP^8)''' = Σ_{β+|M|=3} 3!·(g^{(β)}/β!)·∏_l C(8,M(l))·P^{8−|M|}∏_{r=1}^{|M|}P/(t+l_r)  (M a multiset in [1,n]).
Write P = n!C(t+n,n), P/(t+l) = (l−1)!(n−l)!Y_l, Y_l := C(t+l−1,l−1)C(t+n,n−l), g^{(β)}/β! = 2^βg_β (g_β ∈ ℤ₂[[t]],
Δ ≥ 0). Constants: v₂ ≥ 1 + (8−|M|)(n−log₂(n+1)) + |M|(n−1−2log₂(n+1)) ≥ 8n−2−11log₂(n+1); functions:
Δ ≥ −⌊log₂n⌋ (P3e,c). By (P3a,b): v₂(S_n) ≥ 24n+8+8n−2−11log₂(n+1)−log₂n−1 ≥ **32n + 5 − 12log₂(n+1)**.
Holds on all exact data (n ≤ 300, 383, 447, 511); actual deficit 32n − v₂(S_n) ∈ [−1, 85].

---------------------------------------------------------------------------------------------------

## 6. L4 — archimedean size — **PROVED + NUMERICAL**

G_k(ε) = ε^8R_n(−k+ε) is holomorphic in |ε| < 1. On |ε| = ¼: |(½−ε)_k/(1−ε)_k| = ∏_{r<k}|r+½−ε|/|r+1−ε|
≤ ∏(r+¾)/(r+¾) = 1, same for (½+ε)_{n−k}/(1+ε)_{n−k}; |n−2k+2ε| ≤ n+½. Cauchy:
  |r_{i,k}| ≤ 4^{8−i}(n+½)2^{16n}.
Then |Z_{i+4}| ≤ (i)₄2^{i+4}(n+1)·4^{8−i}(n+½)2^{16n}, and with A_k^{(s)} < (2^s−1)ζ(s) ≤ 1.037·2^s (s ≥ 5):
|ρ₀| ≤ 1.037·Σ_{i=1}^{8}(i)₄2^{20−i}·(n+1)(n+½)2^{16n}. Altogether
  max(|ρ₀|,|Z₇|,|Z₉|,|Z₁₁|) ≤ 3.4·10⁸(n+1)²2^{16n}.
Numerically max_{i,k}|r_{i,k}|/(4^{8−i}(n+1)2^{16n}) ≤ 0.0049 for n ≤ 40 and n ∈ {60,100,150,200}; the
actual log max|coef|/n ≈ 11.082 at n ~ 300–511 (→ 16 log 2 = 11.0904 from below).

---------------------------------------------------------------------------------------------------

## 7. L5 — nonvanishing along n = 2^m − 1 — **PROVED + NUMERICAL**

**Proposition.** Let m ≥ 2, n = 2^m − 1, k₀ = 2^{m−1}. Then v₂(S_n) = 32n + 14 − 11m. In particular S_n ≠ 0.

*Setup.* 2t+1+n = 2(t+k₀) =: 2u. So R_n(t+½) = 2^{24n+8}f(t), f := 2u·P^8·h, h(t) := ∏_{k=0}^{n}(2t+2k+1)^{−8}
∈ ℤ₂[[2t]] (h(0) odd), and S_n = −2^{24n+8}∫f'''(t)dt. It suffices to show v₂(∫f''') = 8n+6−11m.

*Leibniz.* Each term of f''' is indexed by γ ∈ {0,1} (derivative on u), β (on h), and a multiset M in [1,n] of
differentiated linear factors of P^8, γ+β+|M| = 3; it equals
  2·3!·C(M)·u^{1−γ}·(h^{(β)}/β!)·P^{8−|M|}∏_{r}P/(t+l_r),   C(M) := ∏_l C(8,M(l)).
Write it as K·Φ with the constant K := 2·3!·C(M)·n!^{8−|M|}∏_r(l_r−1)!(n−l_r)! and the ℤ₂-valued function
Φ := u^{1−γ}·2^β h_β·C(t+n,n)^{8−|M|}∏_r Y_{l_r}  (h^{(β)}/β! = 2^βh_β, h_β ∈ ℤ₂[[t]], Δ(h_β) ≥ 0).
Valuations: v₂(n!) = n−m; W_l = v₂((l−1)!(n−l)!) ≥ n+1−2m+[l≠k₀] (P7); v₂C(8,1) = 3, v₂C(8,2) = 2,
v₂C(8,3) = 3. All binomials have lower index ≤ n, so Δ ≥ −(m−1) (P3e).

*Key identity.* Since t·C(t+n,n) = (n+1)C(t+n,n+1) and n+1 = 2^m:
  u·C(t+n,n) = 2^{m−1}·Λ(t),   Λ := C(t+n,n) + 2C(t+n,n+1),   Δ(Λ) ≥ min(−(m−1), 1−⌊log₂2^m⌋) = 1−m.
Hence (P3a–c): if γ = 1, Δ(Φ) ≥ β−(m−1), so v₂(∫Φ) ≥ β−m; if γ = 0 (then 8−|M| ≥ 5, so one binomial
C(t+n,n) is available to pair with u), Δ(Φ) ≥ (m−1)+β+(1−m) = β, so v₂(∫Φ) ≥ β−1.

*Dominant term:* γ = 1, β = 0, M = {k₀,k₀}: K = 336·n!^6((k₀−1)!(n−k₀)!)^2, v₂(K) = 4+6(n−m)+2(n+1−2m)
= 8n+6−10m, and Φ = h·C(t+n,n)^6·Y_{k₀}^2 with Y_{k₀} = C(t+k₀−1,k₀−1)C(t+n,k₀−1).
Δ_m(Φ) ≥ 2−m: Δ_m(C(t+n,n)²) ≥ 1−(m−1) (P3e, m > ⌊log₂n⌋ = m−1), the two binomials in Y have lower index
2^{m−1}−1 so Δ ≥ −(m−2), Δ(h) ≥ 0, product rule (P3c). By (P3a),
∫Φ ≡ 2^{−m}Σ_{x=0}^{2^m−1}Φ(x) (mod 2^{1−m}). For 1 ≤ x ≤ 2^m−1, C(x+2^m−1,2^m−1) is even (Kummer: adding
x and 2^m−1 produces a carry), so Φ(x) ≡ 0 (mod 2^6); Φ(0) = h(0)·C(2^m−1,2^{m−1}−1)² is odd (Lucas).
So ∫Φ = 2^{−m}·(unit) and the dominant term has v₂ exactly 8n+6−11m.

*All other terms* have v₂ ≥ 8n+7−11m. With v₂(K) ≥ 2+ΣC + 8n−8m + |M|(1−m) + #{r: l_r ≠ k₀}
(ΣC := Σ_l v₂C(8,M(l))), the two cases give, after adding the bound for ∫Φ,
  v₂(∫term) ≥ 8n+4−11m + ΣC + #{r: l_r≠k₀} + βm     (for both γ = 0 and γ = 1).
 - γ=1, β=0, |M|=2: {k₀,k₀} is the dominant term; {k₀,l}: ΣC+# = 6+1; {l,l}: 2+2; {l,l'}: 6+2 — all ≥ 3.
 - γ=1, β=1: ΣC = 3, βm ≥ 2 ⇒ ≥ 8n+9−11m. γ=1, β=2: βm = 2m ≥ 4 > 3 ⇒ fine for m ≥ 2.
 - γ=0, β=0, |M|=3: ΣC ≥ 3 ({l³}: 3; {l²,l'}: 5; {l,l',l''}: 9). γ=0, β ≥ 1: ΣC + βm ≥ 2+m ≥ 4 or ≥ 3+2m or ≥ 3m.
Hence all non-dominant terms are ≥ 8n+7−11m, v₂(∫f''') = 8n+6−11m and v₂(S_n) = 24n+8+8n+6−11m. ∎

*Numerical confirmation.* (i) ζ₂-based exact ledger: v₂(S_n) = 32n+14−11m for m = 2,…,9
(n = 3,…,511) — e.g. v₂(S₁₂₇) = 4001, v₂(S₅₁₁) = 16267. (ii) Independent Mahler-series computation (no ζ₂
values; mahler_check.out), m = 2..5: v₂(∫f''') = 8, 29, 82, 199 = 8n+6−11m; the normalised dominant integral
∫hC(t+n,n)^6Y² has v₂ = −m exactly; the remainder has v₂ = 8n+7−11m.
*Pattern for other (a,j)* (NUMERICAL, m ≤ 7): v₂(S_{2^m−1}) = 4an + c − (a+j)m with (a,j,c) = (4,1,5), (8,3,14),
(10,3,14) — the same dominant-term count predicts all three.

---------------------------------------------------------------------------------------------------

## 8. L6 — proof of the Theorem — **PROVED** (given L1–L5)

Suppose ζ₂(7), ζ₂(9), ζ₂(11) are all rational. For n = 2^m−1 (m ≥ 2) put L_n := D_nS_n =
a_{n,0}+a_{n,1}ζ₂(7)+a_{n,2}ζ₂(9)+a_{n,3}ζ₂(11), a_{n,·} = D_n·(ρ₀,Z₇,Z₉,Z₁₁) ∈ ℤ (§4.4). By L5, L_n ≠ 0 and
|L_n|₂ ≤ |S_n|₂ = 2^{−(32n+14−11m)}. By L4 and §4.4, max|a_{n,i}| ≤ 3.4·10⁸(n+1)²·exp(11n+o(n))·2^{16n}. So
  max_i|a_{n,i}|·|L_n|₂ ≤ exp((11 − 16 log 2)n + o(n)) = exp(−0.090355n + o(n)) → 0,
contradicting (P4). ∎

*Size of the o(n) terms (explicit, NUMERICAL illustration).* With exact θ, ψ (sieve to 2^27), the proved bound
M(n) := log[3.4·10⁸(n+1)²] + log D_n + 16n log2 − (32n+14−11m+12(m−1))log2 (the last term uses v₂(D_n) =
12(m−1)) is negative for m = 8 and for all 11 ≤ m ≤ 27, with M(n)/n = −0.0903 at m = 27
(margin_explicit.out); it is positive for m ≤ 7 and m = 9, 10 only because ψ(n)/n > 1 there. An explicit
threshold for all larger m follows from explicit PNT bounds (e.g. |θ(x)−x| ≪ x/(log x)²) — SKETCH, not needed.

---------------------------------------------------------------------------------------------------

## 9. Numerical verification inventory (all exact rational arithmetic unless stated)

Code/results in this folder (scratchpad/lai2/prove-7-9-11/):
* `lf.py` — exact partial fractions (log-derivative recursion), ρ₀, Z_i for general (a,j); reproduces LSZ.
* `zeta2.py` — ζ₂(3..13) to 17000 bits via distribution relation + Bernoulli expansion
  (J_s = 2^{−N}Σ_j C(−s,j)B_j2^{s+(N+1)j}Σ_{a<2^N}(2a+1)^{−s−j}); checks J_odd = 0 to 17020 bits and
  agreement across N ∈ {0,4,9}; cached in `zeta2_K17000.json`.
* `run_ledger.py` → `ledger83.jsonl`, `ledger83_summary.csv` (n = 1..300, 383, 447, 511): structure, per-prime
  denominators vs d_n^{11}, v₂(S_n), archimedean size, margins. Summary: S_n ≠ 0 for every tested n;
  odd part of denominator | d_n^{11} always; L3 bound always holds; v₂(S_{2^m−1}) = 32n+14−11m for m = 2..9.
  Agrees with the earlier project numbers (32n−v₂ = 18, 27, 63, 11, 20, 29 at n = 80, 100, 127, 128, 160, 200).
* `andrews_check.py` → `andrews_check.out`: Andrews identity (n ≤ 6), ρ₀ residue formula, closed form of
  F_J(0), p-adic claim v_p(F_J(0)) ≥ −4 (200000 samples). `extra_checks.py`: identity for n = 7, 8;
  residue bound; integrality d_n^{8−i}r_{i,k}, d_n^{12}ρ₀; Z denominators.
* `perell_check.py`: v_p([ε^7]T_{n,ℓ}) ≥ −11 for all ℓ, n ∈ {18,22,26,30} (attained).
* `mahler_check.py` → `mahler_check.out`: independent (Mahler-series) confirmation of L5 for m = 2..5.
* `l5_bookkeeping.py` → `l5_bookkeeping.out`: enumerates every Leibniz class (γ, β, multiset type of M) with the
  exact bounds of §7 and confirms "non-dominant ≥ dominant + 1" for m = 2..40 (tightest class: γ=0, β=0,
  M = {k₀,k₀,k₀}, whose true valuation is indeed dominant + 1).
* `bigprime_pattern.py` → `bigprime_pattern.out`; `margin_explicit.py` → `margin_explicit.out`.

---------------------------------------------------------------------------------------------------

## 10. Margin: can prime-selective savings or 2-adic divisibility make it safer than −0.09?

* The LSZ-type Φ_n of §4.4 is *exactly* the saving from the trivial d_n^{12} (a+j+1) to d_n^{11} (a+j); it is
  already used and is what makes the exponent 11 − 16 log 2 = −0.0904 (with d_n^{12} it would be +0.91).
* Beyond d_n^{11}: for primes p ∈ (√(2n), n] the exact exponent of p in the denominator of ρ₀ is 11 for all but
  0–2 sporadic primes per n (no pattern in {n/p}: e.g. n=511: p = 41, 233 with exponent 10), total saving
  ≈ 0.02n at n ≤ 511 and apparently o(n); primes ≤ √(2n) contribute O(√n log n). So **no Lai-type
  {n/q}-selective saving exists for this family**; the asymptotic exponent −0.0904 cannot be improved through
  denominators. (Lai's Φ_n comes from factorial ratios (4k)!(4n−4k)!/…; here G_k(0) = (n−2k)(C(2k,k)C(2n−2k,n−k))^8
  has min_y([y ≥ ½] + [{x−y} ≥ ½]) = 0, so no uniform divisibility.)
* The ζ-coefficients have better denominators (d_n^4, d_n^2, 1) but ρ₀ dominates, so irrelevant.
* 2-adic divisibility cannot help: |a|_∞·|L|₂ is invariant under multiplying/dividing the form by powers of 2
  (so the 2-part 2^{12(m−1)} of D_n is neutral, and a common 2-power in the coefficients would be neutral too).
  Along n = 2^m−1 the 2-adic loss is exactly 11m − 14 = O(log n), i.e. nothing linear is lost 2-adically.
* Conclusion: the proof works with the thin but genuine asymptotic margin −0.090355·n; in the explicit
  illustration the proved bound becomes < 1 from n = 2^{11}−1 on (within the computed range).

---------------------------------------------------------------------------------------------------

## 11. Remarks, variants, open ends

1. **Relation to "13".** Our statement implies Lai's s = 3 case (7,9,11,13). The same method with
   (a,j) = (10,3) (R = 2^{20n}(2t+n)(t+½)_n^{10}/(t)_{n+1}^{10}, forms in 1, ζ₂(7..13)) has asymptotic exponent
   13 − 20 log 2 = −0.863 and numerically v₂(S_{2^m−1}) = 40n + 14 − 13m (m ≤ 7), i.e. it would re-prove Lai's
   {7,9,11,13} with a comfortable margin (L2c generalises verbatim; the L5 case check for binomial
   coefficients C(10,·) was not redone — SKETCH/NUMERICAL).
2. **General (a,j)** (even a, odd j ≤ a−3): L1, L2 (denominator d_n^{a+j} after the Andrews saving, since
   F_J(0) carries (2ℓ−1)^{−(j+1)}/(J_a+1) and a−1 derivatives), L3, L4 generalise; exponent (a+j) − 2a log 2.
   Only (8,3) gives a triple; (6,3) {7,9} has +0.68 (fails).
3. **Alternative nonvanishing (SKETCH).** Lai–Sprang's criterion (2306.10393, Lemma 2.2) would give S_n ≠ 0 for
   all large n if one proves v_p(ρ₀) = −11 exactly for some prime p ∈ (√(2n), n] (then v_p(D_nρ₀) = 0 while
   v_p(D_nZ_i) ≥ 7). Numerically true for almost all such p, but not proved here; not needed.
4. **Recurrence route (not pursued).** The solution space of the n-recurrence satisfied by S_n contains the
   j = 1, 3, 5 forms (all share c₃, c₅, c₇), so a 4×4 Casoratian argument à la LSZ is unlikely to close;
   Lai's subsequence method is the right tool here.
5. Everything in §§3–8 is self-contained modulo (P1)–(P8), which are published results.
