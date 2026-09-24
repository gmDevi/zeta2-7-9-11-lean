# Blueprint: at least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational

Lean 4 + Mathlib formalisation of the (new, unrefereed) proof in `proof.md`
(scratchpad `lai2/prove-7-9-11/proof.md`). It sharpens Lai (IJNT 2025, arXiv:2304.00816), whose
result also needed ζ₂(13). The family is the (a, j) = (8, 3) member of the LSZ family
(Lai–Sprang–Zudilin, arXiv:2505.05005):

    R_n(t) = 2^{16n} (2t+n) (t+1/2)_n^8 / (t)_{n+1}^8,     S_n = -∫_{Z_2} R_n'''(t + 1/2) dt.

## Main theorem (`Zeta2Lean/Main.lean`)

```lean
theorem Zeta2.zeta2_7_9_11_not_all_rational (hPNT : PNT_Stmt) (hAndrews : Andrews_Stmt) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q) ∧ (∃ q : ℚ, zeta2 11 = q))
```

* `HasVolkenborn f I`: the Riemann sums `2^{-N} ∑_{x<2^N} f x` tend to `I` in `ℚ_[2]`. The Volkenborn
  integral is not in Mathlib, so it is defined through these sums (`Defs.lean`).
* `J s = limUnder` of the Riemann sums of `(x+1/2)^{-s}`. The first conjunct proves they converge,
  so junk values of `limUnder` cannot enter.
* `zeta2 s = J (s-1) / ((s-1) 2^s)`. LSZ Lemma 2.8 identifies this with the Kubota–Leopoldt value
  ζ₂(s) = L₂(s, ω^{1-s}). That identification is a **cited normalisation and is not formalised**.
  Irrationality does not change under the non-zero rational factor `(s-1) 2^s`, so the theorem about
  `J 6, J 8, J 10` is the mathematical theorem.

`#print axioms` (end of `Main.lean`) should show only `propext, Classical.choice, Quot.sound` once
the proof files are complete. Since prove round 1 (2026-09-24) it does: all 24 proof files are complete. See
`STATUS.md` for the current census.

## Cited hypotheses (theorem parameters, never axioms)

| name | statement | why it is cited |
|---|---|---|
| `PNT_Stmt` | `Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)` | Needed for `log D_n = 11n + o(n)`: the margin is only `11 − 16 log 2 = −0.0904` per n, and Chebyshev-type bounds are far too weak. Only the upper half, `ψ(x) ≤ (1+δ)x`, is used. PNT is proved in Lean in PrimeNumberTheoremAnd but is not in Mathlib. `Chebyshev.psi` is Mathlib's (`ψ n = log lcm(1..n)`). |
| `Andrews_Stmt` | Andrews' transformation of a terminating very-well-poised `₂ₘ₊₅F₂ₘ₊₄` into an m-fold sum (Andrews 1975 Thm 4, q→1; Krattenthaler–Rivoal, Mém. AMS 186 (2007), Théorème 8, verbatim), in full generality: all `m, N`, every field of characteristic 0, all displayed denominators non-zero. `(a/2+1)_κ/(a/2)_κ` is written `(a+2κ)/a`. | This is the only known route to the one-power denominator saving L2c (d_n^{12} → d_n^{11} for primes > √(2n)). Without that saving the exponent is +0.91 and the proof fails. A Lean proof of the transformation (iterated Whipple ₇F₆→₄F₃ plus Pfaff–Saalschütz) would be a separate project. **Tested:** `python/mirror.py` checks the identity exactly at 140 random rational parameter sets (m ≤ 3, N ≤ 5), and checks the specialisation used here at random rational ε. |

Nothing else is assumed. `scripts/audit.sh` reports no `axiom`, `native_decide` or similar.

## Architecture

```
Zeta2Lean/Defs.lean        all definitions + a few proved API lemmas (volkenbornSum_add, HasVolkenborn.sum,
                           halfPow_eq_cast, mem_chains, chainPrev_le, Phi_dvd_dn, Dn_pos, Dn_mul_Phi, ...)
Zeta2Lean/Statements.lean  one Stmt_X : Prop per lemma (structures with named fields for Δ-calculus etc.)
Zeta2Lean/Assembly.lean    main_of_stmts : Stmt_JConv → Stmt_L1 → Stmt_L2cor → Stmt_L4 → Stmt_L5 →
                           Stmt_Asymptotic → Stmt_Criterion → PNT_Stmt → MainStatement   (complete, no sorry)
Zeta2Lean/Proofs/*.lean    theorem X_proof (deps as hypotheses) : Stmt_X   (24 files; stubs in the blueprint,
                           all proved in prove round 1, see STATUS.md)
Zeta2Lean/Main.lean        wires everything; #print axioms
python/mirror.py           exact-arithmetic mirror of Defs.lean + numerical checks of every Stmt
python/audit_independent.py, python/jcheck_bernoulli.py   independent re-implementation (audit, see below)
```

Proof files import only `Zeta2Lean.Statements`. They receive their dependencies as hypotheses, so they
can be elaborated independently with `scripts/check.sh`.

## Statement map (Stmt ↔ proof.md ↔ proof file)

| Stmt | content | proof.md | file | deps |
|---|---|---|---|---|
| `Stmt_JConv` | Riemann sums of `(x+1/2)^{-s}` converge (to `J s`) | P1, P2 | `JConvergence` | – |
| `Stmt_Translation` | `∫ f(t+k) = ∫ f − s ∑_{ℓ<k} (ℓ+1/2)^{-s-1}` for `f = (t+1/2)^{-s}` | P1 (LSZ 2.4) | `Translation` | – |
| `Stmt_Criterion` | Lai's criterion (integers, `B_m‖L_m‖₂ → 0`, `L_m ≠ 0` frequently) | P4 (Lai 2.1) | `Criterion` | – |
| `Stmt_PF` | partial fractions `R_n = ∑ r_{i,k}(t+k)^{-i}`: polynomial form and Taylor form | §3 "useful formula" | `PartialFractions` | – |
| `Stmt_CoeffVanish` | `r_{i,n-k} = (−1)^{i+1} r_{i,k}`, `c₁ = 0`, `c_even = 0` | §3 Lemma 1 | `CoeffVanish` | PF |
| `Stmt_L1` | `S_n = ρ₀ + 60c₃J₆ + 210c₅J₈ + 504c₇J₁₀` (= `ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9) + Z₁₁ζ₂(11)`) | §3 Lemma 1 | `LinearForm` | JConv, Translation, CoeffVanish |
| `Stmt_BlockF` | `d_n^j [ε^j] 4^n (1/2−ε)_k(1/2+ε)_{n−k}/n! ∈ ℤ` | P5 | `BuildingBlock` | – |
| `Stmt_L2a` | `d_n^{8−i} r_{i,k} ∈ ℤ` | §4.1 | `DenomL2a` | BlockF |
| `Stmt_L2b` | `d_n^{12} ρ₀ ∈ ℤ` (root trick) | §4.2 | `DenomL2b` | PF, L2a |
| `Stmt_ResidueForm` | `ρ₀ = −24 ∑_ℓ [ε^7] T_{n,ℓ}` | §4.3 Step 1 | `ResidueForm` | – |
| `Stmt_AndrewsApplied` | `T_{n,ℓ} = ∑_{J} F_J` (8-fold chains) | §4.3 Steps 2–3 | `AndrewsApplied` | **Andrews** (cited) |
| `Stmt_FJClosed` | `F_J(0)` = explicit binomial product `FJ0` | §4.3 Step 4 | `ClosedFormFJ` | – |
| `Stmt_FJKummer` | `v_p(FJ0) ≥ −4` (p ≥ 11, p² > 2n) | §4.3 Step 5 | `KummerFJ` | – |
| `Stmt_L2c` | `v_p(ρ₀) ≥ −11` (p ≥ 11, p² > 2n) | §4.3 Step 6 | `DenomL2c` | ResidueForm, AndrewsApplied, FJClosed, FJKummer |
| `Stmt_L2cor` | `D_n = d_n^{12}/Φ_n` makes `ρ₀, Z₇, Z₉, Z₁₁` integral | §4.4 | `DenomCor` | L2a, L2b, L2c |
| `Stmt_L4` | `max(|ρ₀|,|Z_i|) ≤ C (n+1)^A 2^{16n}` (some C, A) | §6 | `ArchBound` | – |
| `Stmt_Asymptotic` | PNT ⇒ `D_n · C(n+1)^A 2^{16n} · 2^{−(32n+14−11m)} → 0` along `n = 2^m−1` | §4.4, §8 | `Asymptotics` | (PNT inside) |
| `Stmt_Delta` | Δ-calculus: Riemann-sum congruences, sums, scalars, products | P3(a)–(c) | `DeltaCalculus` | – |
| `Stmt_DeltaFun` | Δ of binomials, binomial squares, `h_β` | P3(d),(e) | `DeltaFunctions` | Delta |
| `Stmt_Digit` | `v₂((2^m−1)!)`, Lai's digit lemma | P7 | `Digits` | – |
| `Stmt_Leibniz` | `integrand n x = ∑_{γ,β,M} leibTerm` | §7 Setup/Leibniz | `Leibniz` | PF |
| `Stmt_LeibTermBound` | `Δ(leibTerm) ≥ 32n+13−11m+βm+∑v₂C(8,M_l)+#` | §7 Valuations/Key identity | `LeibnizTermBound` | Delta, DeltaFun, Digit |
| `Stmt_L5Dom` | dominant term: `Δ_m ≥ target+2`, level-m Riemann sum has `v₂ = target` exactly | §7 Dominant term | `DominantTerm` | Delta, DeltaFun, Digit |
| `Stmt_L5` | `v₂(S_{2^m−1}) = 32n+14−11m` (so `S_n ≠ 0`) | §7 | `Nonvanishing` | Delta, Leibniz, LeibTermBound, L5Dom |
| `MainStatement` | theorem | §8 (L6) | `Assembly.lean` (done) | JConv, L1, L2cor, L4, L5, Asymptotic, Criterion, PNT |

L3 (`v₂(S_n) ≥ 32n + 5 − 12 log₂(n+1)` for all n) is **not needed**. It is not formalised.

## Dependency graph

```
                               MainStatement  (Assembly.lean, done)
   ┌──────────┬─────────┬──────────┬──────┬───────────┬────────────┬──────────┐
 JConv       L1       L2cor       L4     L5       Asymptotic   Criterion    PNT (cited)
            / | \      / | \               \
   JConv Transl CoeffV L2a L2b L2c          L5 ← Delta, Leibniz, LeibTermBound, L5Dom
                  |    |   | \   \               Leibniz ← PF
                  PF BlockF PF L2a \             LeibTermBound, L5Dom ← Delta, DeltaFun, Digit
                                  L2c ← ResidueForm, AndrewsApplied, FJClosed, FJKummer
                                        AndrewsApplied ← Andrews (cited)
                                        DeltaFun ← Delta
```

Leaves (no dependencies): JConv, Translation, Criterion, PF, BlockF, ResidueForm, FJClosed, FJKummer,
L4, Asymptotic, Delta, Digit. AndrewsApplied depends only on the cited Andrews statement.
All 24 files can be worked on at the same time. Each file sees its dependencies only as hypotheses.

## Key design decisions

1. **Riemann sums instead of integrals.** L5 is proved entirely at the level of Riemann sums.
   `Stmt_Delta.riemann` gives `‖R_M − R_m‖ ≤ 2^{1−c}` from `Δ_m ≥ c` without assuming convergence,
   so the dominant term never needs its own convergence proof.
2. **Partial-fraction coefficients by an explicit formula.** `r_{8−μ,k} = [ε^μ] 2^{16n}(n−2k+2ε)Ψ_k(ε)^8`
   is computed in `PowerSeries ℚ`. `Stmt_PF` links it to the product form of `R_n`.
3. **Integrand in partial-fraction form.** `integrand n x = ∑ (i)₃ r_{i,k} (x+k+1/2)^{-i-3}`. This
   makes L1 a matter of linearity. L5 goes through `Stmt_Leibniz`, which uses PF.
4. **No `δ → 0` limit in the Andrews step.** At δ = 0 every denominator on both sides is non-zero,
   so `Andrews_Stmt` is applied with `(b₉, c₉) = (1, 1+a+N)` directly, in any field containing
   `ℚ⟦ε⟧` (`FractionRing (PowerSeries ℚ)` or `LaurentSeries ℚ`).
5. **The derivative lemma in L2c avoids log/exp.** Each linear factor `c + dε` of `F_J` has
   `v_p(d/c) ≥ −1`, so `F_J/F_J(0)` lies in the monoid of "p-tame" series (`v_p([ε^j]) ≥ −j`).
6. **Existential constants in L4.** Any bound `poly(n)·2^{16n}` suffices, and elementary majorants
   are recommended over Cauchy estimates.
7. **Valuation statements.** Where zero could give a junk valuation, statements use norms or
   `padicValRat` lower bounds that are negative, which hold trivially for 0.

## Numerical mirror (`python/mirror.py`)

The mirror is pure standard-library Python with exact `Fraction` arithmetic. Each Lean definition
is transcribed literally, including natural-number truncated subtraction. Run it with
`python3 python/mirror.py [--quick]`. It needs `python/zeta2_K17000.json` (J-values to 17000 bits)
and optionally `python/lf_reference.py` for an independent cross-check.

What it checks:

* `rcoef`, `rho0` and the Z's against the independent log-derivative code (`lf.py`), for n ≤ 15.
* `PF.poly` (n ≤ 6) and `PF.series` at random rational y.
* `CoeffVanish`, BlockF, L2a and L2b integrality.
* ResidueForm; AndrewsApplied and FJClosed for every chain; FJKummer on random critical-biased samples.
* L2c and L2cor.
* The Andrews identity at random rational parameters.
* L4 with C = 3.4e8, A = 2.
* The asymptotic exponent with exact ψ and θ, along n = 2^m − 1.
* DeltaFun, Digit and Leibniz.
* LeibTermBound on finite ranges, with minimum slack 0 attained at γ = 0, β = 0, M = 3·[k₀].
* `domTerm = leibTerm(1, 0, 2·[k₀])`.
* L5Dom: the level-m Riemann sum has exact valuation, m ≤ 5.
* L5: `v₂(S_{2^m−1}) = 32n + 14 − 11m` exactly, m = 2..7, using the J-values.
* JConv, Translation and L1: 2-adic convergence of the Riemann sums of the Lean definitions to the
  cached J-values.

The quick run (`--quick`) takes about 4 minutes and the full run about 6 minutes; both pass all
checks. The full-run log is `python/mirror_full.log` (0 checks failed; `v₂(S_{127}) = 4001`).

## Workflow for provers

* Elaborate one file: `wsl -d Ubuntu --cd /home/mdevi/zeta2-lean -- bash scripts/check.sh Zeta2Lean/Proofs/Foo.lean`.
* Never edit `Defs.lean` or `Statements.lean`. If a statement looks wrong or unprovable as written,
  report it to the architect with a counterexample from the mirror.
* Put helper lemmas inside your own proof file, in `namespace Zeta2`, with distinctive names to avoid
  clashes in `Main.lean`. Private lemmas are recommended.
* Scratch work goes in `Zeta2Lean/Scratch/<yourname>_*.lean`. Delete it when done.

## Scope of the result (how far the method generalises)

* The method proves **at least one of** ζ₂(7), ζ₂(9), ζ₂(11) is irrational. It does **not** give
  two of the three. The criterion (P4) uses a single sequence of linear forms in 1, ζ₂(7), ζ₂(9),
  ζ₂(11) with integer coefficients, so it can only rule out "all three rational". Getting "at least
  two irrational" would need forms that eliminate one of the values, or a linear-independence
  criterion (Nesterenko/Siegel type) with several independent forms. Neither is available here, and
  the margin (−0.09 per n) leaves no room for such losses.
  Equivalently, the theorem says `dim_ℚ span{1, ζ₂(7), ζ₂(9), ζ₂(11)} ≥ 2`; "two of three" would follow
  from `dim ≥ 3`, which one sequence of forms cannot give.
* Other (a, j): heuristically (L1, L2 with the Andrews saving d_n^{a+j}, L4, and an L5 dominant term)
  the exponent is `(a + j) − 2a log 2`. The only new triple is (8, 3) ((8, 1) gives {5, 7, 9}, which
  contains the known-irrational ζ₂(5)). (10, 3) would give Lai's {7, 9, 11, 13} again with margin −0.86,
  but its L5 case analysis (binomials C(10, ·)) is only numerical/sketch (proof.md §11). (6, 3) would give
  {7, 9} but has exponent +0.68, so it fails; no (a, j) gives a new pair.
* In the Lean development, (a, j) = (8, 3) is hard-wired: `Gser` has `Psi^8` and `2^{16n}`; `integrand`
  has `(i)₃`; the `Z` constants; `Fser` / `chains 8`; and the L5 slack count with `v₂ C(8, ·)`. The
  formal conclusion is exactly `¬ (ζ₂(7) ∈ ℚ ∧ ζ₂(9) ∈ ℚ ∧ ζ₂(11) ∈ ℚ)`, and `Stmt_Criterion` (one
  sequence of forms) can conclude nothing stronger. For another (a, j):
  - JConvergence, Translation, Criterion, DeltaCalculus, DeltaFunctions and Digits carry over unchanged;
  - the other files would need re-parametrised definitions.

## Audit (adversarial faithfulness check, 2026-09-24)

Every definition and `Stmt_*` was re-derived by hand against proof.md §§2–8 (indices, ranges, the `1/2`
shifts, `(i)₃` in `integrand` vs `(i)₄` in `rho0`, `Z`-constants, signs, natural-number subtraction) and
re-tested with code written independently of `mirror.py` (`python/audit_independent.py`, exact
`Fraction`s). No false or unfaithful statement was found. Checked:

* `rcoef` (Ψ-formula) = Laurent coefficients computed factor by factor from the product form (n ≤ 20);
  `R_n(t) = ∑ r_{i,k}(t+k)^{-i}` at random rational t; `PF.series`; symm/c₁/c_even (n ≤ 24);
  L1 as an exact algebraic identity (J symbolic, n ≤ 15); n = 0, 1 values of proof.md.
* BlockF for **all** j (n ≤ 40); L2a, L2b, L2c, L2cor for n ≤ 150; ResidueForm n ≤ 12;
  AndrewsApplied at random rational ε and FJClosed for all chains, n ≤ 10; FJKummer exhaustively on
  critical chains (p = 11, 13, 17; minimum −4, attained).
* `Andrews_Stmt` (cited): matches Krattenthaler–Rivoal Théorème 8, (6.1) verbatim (incl. the m = 0
  convention); exact at 316 generic and 850 degenerate (half-integer) parameter sets, m ≤ 5 and m = 8,
  and in the specialisation used by AndrewsApplied (all hypotheses hold there).
* Leibniz: `integrand` = `−6[ε³]R_n(x+½+ε)` (product form) = ∑ `leibTerm` (n ≤ 6); LeibTermBound
  (m = 2, 3 all terms, m = 4 sampled; minimum non-dominant slack 0 at γ = β = 0, M = 3·[k₀]); L5Dom.
* L5 at the Riemann-sum level: `v₂(R_M(integrand)) = target m` for all tested `M ≥ m`, m = 2..5 (no
  J-values used); and in the limit, with J-values recomputed from the Bernoulli moments
  `J_s = 2^s ∑_j C(−s,j) 2^j B_j` (`python/jcheck_bernoulli.py`), which agree with the cache to > 1140
  bits: `v₂(S_n) = 88, 205, 450, 951` for m = 2..5.
* `zeta2` normalisation checked against LSZ Lemma 2.8; `PNT_Stmt` uses Mathlib's
  `Chebyshev.psi x = ∑_{n ≤ ⌊x⌋} Λ(n)` (standard ψ). PNT is not in this Mathlib (only Chebyshev bounds
  and ζ-nonvanishing on Re s = 1 are), so it must stay cited; no Kubota–Leopoldt ζ₂ exists in Mathlib,
  so the LSZ identification stays a documented citation.
* `#print axioms Zeta2.main_of_stmts`: `propext, Classical.choice, Quot.sound`.

Changes made by the audit: `mem_chains`, `chainPrev_le` added (proved) to `Defs.lean`; two
non-existent lemma names in hints fixed (`Nat.eq_one_of_self_dvd` in DenomL2b, `padicValRat.prod` /
`mem_chains` in KummerFJ); chain-API pointers added to ClosedFormFJ and DenomL2c.

## Second audit (Lean-soundness lens, 2026-09-24)

Independent of the audit above; looked for Lean-specific ways the formal theorem could be false,
vacuous or unprovable. **No unsound, vacuous or unprovable statement was found.** `Defs.lean`,
`Statements.lean`, `Assembly.lean` and `Main.lean` are unchanged.

* **Junk values.** Every `⁻¹` in `PowerSeries ℚ` (Mathlib: `φ⁻¹ = 0` iff constant coefficient `0`) has a
  non-zero constant term (`Psi`, `Tser`, `Pser`, `Fser`, `hcoef`). The one exception is `Rser`, where
  `PF.series` assumes `y + j ≠ 0`. Every rational/2-adic division is by a non-zero quantity: `halfPow`,
  `Ahalf`, `integrand`, `zeta2` at 7, 9, 11, and `FJ0` for `ℓ ≥ 1`. `Dn` is an exact ℕ-division
  (`Dn_mul_Phi`). Every ℕ-subtraction is guarded by the hypotheses of the statement that uses it (`8-i`,
  `n-k`, `k-ℓ`, `ℓ-1`, `n-ℓ-J_i`, `J_i - chainPrev`, `x+l-1`, `2^m-1-2^{m-1}`, `3-γ-β`, `2^m-2m` for
  `m ≥ 2`). Casts go `ℕ → ℚ` before any subtraction. `zpow` is only used with base 2 in `ℝ`. `limUnder`
  (`J`) is certified by the first conjunct of the theorem; `Sn` is unused. Ranges match proof.md
  (`range (n+1)` = `0..n`, `Icc 1 8`, `Icc ℓ n`, `range k` = `ℓ₀ < k`). `dn 0 = 1` (`Nat.lcmUpto n =
  (Icc 1 n).lcm id`).
* **No auto-bound implicits.** The lakefile keeps `autoImplicit` on for single letters. `#check
  (Stmt_X : Prop)` succeeds for all 24 statements, `PNT_Stmt`, `Andrews_Stmt` and `MainStatement`.
  Every definition has exactly its intended arguments.
* **Cited hypotheses are true, so the theorem is not vacuous.**
  - `PNT_Stmt`: `Chebyshev.psi x = ∑_{n ∈ Ioc 0 ⌊x⌋₊} Λ n`, so this is exactly PNT.
  - `Andrews_Stmt`: every denominator on either side is `a`, a factorial, or `(x)_κ` / `(x)_{i_k}` with
    `κ, i_k ≤ N`. Since `(x)_κ ∣ (x)_N`, the hypotheses make every one of them non-zero. So the Lean
    statement is exactly the rational-function identity of KR Thm 8, evaluated where it is defined; there
    is no `x/0 = 0` loophole.
  - Re-tested with a new literal transcription of the Lean statement (scratch `lens2.py`, not
    derived from `mirror.py` / `audit_independent.py`): 676 admissible random points (generic,
    half-integer, `a ∈ ℤ_{<0}`, `b_k = c_k`; m ≤ 3, N ≤ 4) plus 30 points of the m = 8 specialisation.
    Zero failures.
  - The same script also confirms `AndrewsApplied` (30 random rational ε, n ≤ 5), `FJClosed` (1001
    chains), `ResidueForm` (n ≤ 6), and `v₂(R_M(integrand)) = target m` for m = 2, 3 and M = m..m+3.
    All are exact.
  - LSZ Lemma 2.8 (re-read in `lsz.txt`) is purely multiplicative: `J_{s-1} = (s-1) 2^s ζ₂(s)`.
* **Assembly / axioms.** `#print axioms`: `main_of_stmts` and `linear_form_zeta` →
  `[propext, Classical.choice, Quot.sound]`; `zeta2_7_9_11_not_all_rational` → the same plus `sorryAx`
  (stubs only). There are no axiom declarations.
* **Hints.** All ≈ 250 Mathlib names quoted in the 24 stub docstrings were `#check`ed and exist in this
  Mathlib, with the quoted signatures. The only failures are math symbols, the field shorthand below, and
  the deliberately negative mention of `padicValRat.prod`. `ℚ_[2]` has `IsUltrametricDist`,
  `CompleteSpace` and `NormedField` instances, so the ultrametric hints apply.

Fixes made by the second audit:
1. **AndrewsApplied (usability, would have blocked the prover).** Neither `CharZero (FractionRing ℚ⟦X⟧)`
   nor `CharZero (LaurentSeries ℚ)` (nor `CharZero ℚ⟦X⟧`) is found by instance search, and
   `Andrews_Stmt` requires `[CharZero K]`. The docstring now gives a compiled recipe:
   `charZero_of_injective_algebraMap (algebraMap ℚ K).injective`, a specialisation
   `hA (FractionRing (PowerSeries ℚ)) 8`, and a compiled lemma transporting power-series inverses into `K`.
2. **`scripts/audit.sh`.** The census missed declarations behind modifiers or attributes (`private axiom`,
   `@[simp] axiom`, `protected axiom`, `noncomputable opaque`, `private unsafe def`) and
   `Lean.trustCompiler`. The regex is hardened and was tested on synthetic cases. `#print axioms` in
   `Main.lean` remains the definitive check.
3. **LeibnizTermBound, DominantTerm, Nonvanishing.** The shorthand `Delta.x` / `DeltaFun.x` / `Digit.x` is
   now spelled out as the hypothesis fields `hD.x` / `hF.x` / `hG.x`. DominantTerm gets the (compiled)
   ℕ-rewrites `x + l - 1 = x + (l - 1)` and `2^m - 1 - 2^{m-1} = 2^{m-1} - 1`.

## Discharging the cited hypotheses (`Zeta2Lean/Cited/`, blueprint 2026-09-24)

Target (`Zeta2Lean/Cited/Main.lean`):

```lean
theorem Zeta2.zeta2_7_9_11_not_all_rational_unconditional : MainStatement :=
  zeta2_7_9_11_not_all_rational PNT_proof Andrews_proof
```

`Defs.lean`, `Statements.lean`, `Assembly.lean`, `Main.lean` and `Proofs/` are **frozen**. The
kernel-checked main theorem is reused as it is, and `PNT_Stmt` and `Andrews_Stmt` are proved as
theorems. The root `Zeta2Lean.lean` does **not** import `Cited` yet, so the verified default build is
unchanged. Build the new tree explicitly with `bash scripts/build.sh Zeta2Lean.Cited.Main`. Nothing
changes in `lakefile.toml`, `lake-manifest.json` or `lean-toolchain`.

### Architecture (same pattern as the main development)

```
Zeta2Lean/Cited/Defs.lean        Andrews-track definitions (BP, unitα/β, bw, bα, bβ, chainFactor, Achain,
                                 Bchain) + proved API (rpoch_add/succ/succ', rpoch_ne_zero_of_le,
                                 rpoch_negN_mul, rpoch_reflect, fact_ne, Fin.snoc lemmas on chains)
Zeta2Lean/Cited/Statements.lean  one Stmt_X : Prop per sub-lemma (namespace Zeta2.Cited)
Zeta2Lean/Cited/Assembly.lean    pnt_of_stmts, bpChain_of_stmts, andrews_of_bpChain, andrews_of_stmts
                                 (complete, no gaps)
Zeta2Lean/Cited/Proofs/*.lean    theorem X_proof (deps as hypotheses) : Stmt_X
Zeta2Lean/Cited/Vendor/PNT/*.lean  Wiener–Ikehara, vendored from mathlib4 PRs (Apache 2.0, LICENSE there)
Zeta2Lean/Cited/Main.lean        PNT_proof, Andrews_proof, the unconditional theorem, #print axioms
python/cited_mirror.py           exact mirror (Lean semantics) + numerical checks of every new statement
docs/cited/                      the Andrews scout's complete proof and checks (reference, not built)
```

### Statement map

| Stmt | content | file | deps | status |
|---|---|---|---|---|
| `Stmt_WienerIkehara` | Wiener–Ikehara, unbundled: `f ≥ 0`, `∑_{i<n}|f i| ≤ C n`, `LSeries f` summable for `σ > 1`, `LSeries f s - A/(s-1)` extends continuously (`G`) to `re s ≥ 1` ⇒ `(∑_{n ≤ x} f n)/x → A` | `Proofs/WienerIkehara` (wrapper) ← `Vendor/PNT/WienerIkehara` ← `Vendor/PNT/SchwartzCompactSupport` | – (vendored imports) | wrapper complete; both vendored files are stubs |
| `Stmt_PPS` | polynomial Pfaff–Saalschütz in every field: `∑_s C(M,s)(x)_s(y)_s(z-x-y)_{M-s}(z+s)_{2M-s} = (z-x)_M(z-y)_M(z+M)_M` | `Proofs/PfaffSaalschutz` | – | stub |
| `Stmt_UnitPair` | `(unitα a, unitβ)` is a Bailey pair at every level (`a ≠ 0`, char 0) | `Proofs/UnitPair` | – | stub |
| `Stmt_BaileyLemma` | one Bailey step preserves `BP` at level `n` (needs `BP` at all `j ≤ n`, `(1+a-ρ)_n, (1+a-σ)_n ≠ 0`) | `Proofs/BaileyLemma` | PPS | stub |
| `Stmt_SumChainsSucc` | `∑_{chains (m+1) n} f = ∑_{j ≤ n} ∑_{i' ∈ chains m j} f (Fin.snoc i' j)` | `Proofs/ChainSum` | – | stub |
| `Stmt_ChainStep` | `Achain`/`Bchain` for `m+1` pairs = one Bailey step applied to those for `m` pairs (`Fin.init`); base case from the unit pair | `Proofs/ChainStep` | SumChainsSucc | stub |
| `Stmt_BPChain` | `(Achain, Bchain)` is a Bailey pair up to level `N` | `Assembly` (`bpChain_of_stmts`) | UnitPair, BaileyLemma, ChainStep | done |
| `PNT_Stmt` | `ψ(x)/x → 1` | `Assembly` (`pnt_of_stmts`) | WienerIkehara | done |
| `Andrews_Stmt` | KR Théorème 8 | `Assembly` (`andrews_of_bpChain`) | BPChain | done |

Dependency graph:

```
PNT_Stmt ⇐ WienerIkehara   (Vendor/PNT/WienerIkehara ⇐ Vendor/PNT/SchwartzCompactSupport, by import)
Andrews_Stmt ⇐ BPChain ⇐ UnitPair, BaileyLemma ⇐ PPS, ChainStep ⇐ SumChainsSucc
```

All seven open files (five Andrews stubs, two vendored files) can be worked on at the same time. The
vendored `WienerIkehara` builds against the *stub* of `SchwartzCompactSupport`, which already exports the
final statement of `SchwartzMap.dense_hasCompactSupport`.

### PNT route: vendor Wiener–Ikehara from open mathlib4 PRs

Source: PR #43238 at head `78e1b2bbd0d256081c926fccada84fd084653286` (fork `teorth/mathlib4`). It contains
PR #43233 (`Mathlib/NumberTheory/LSeries/WienerIkehara.lean`) and PR #43046
(`Mathlib/Analysis/Distribution/SchwartzSpace/CompactSupport.lean`). The PR base is master `a4c8ef0a69`
(Lean v4.34.0-rc2), 181 commits and one week behind our pin `065356127b` (v4.35.0-rc2). The code is
adapted from PrimeNumberTheoremAnd and is sorry-free upstream. The Mathlib inputs are already in our
pin: `LFunctionResidueClassAux`, its continuity on `re s ≥ 1` (non-vanishing of `ζ` on `re s = 1`),
`eqOn_LFunctionResidueClassAux`, and Chebyshev's `ψ x ≤ (log 4 + 4) x`. The glue from `WeakPNT.lean`
(about 40 lines) is `Cited/Assembly.lean`, with Wiener–Ikehara as a hypothesis.

Vendoring policy:
* Copy the upstream text verbatim. The only header edits: delete `module`; replace the imports by
  `import Mathlib` (plus the other vendored file); delete `@[expose] public section`.
* Keep every declaration name. None exists in our pin.
* Keep the upstream copyright headers and the Apache-2.0 `LICENSE` (copied from Mathlib).
* Fix drift errors locally and list every deviation under "Porting notes" in the file's docstring.

Rejected alternatives:
* Depending on PrimeNumberTheoremAnd: it pins Lean v4.33.1 and Mathlib `0df444a360`, with
  LeanArchitect, leancert and PrimeCert.
* Porting PNT+ itself: about 3,170 lines across 1,100 commits.
* Newman's proof from scratch.

**Future swap.** Once Mathlib contains the PRs and the project deliberately bumps Mathlib, delete
`Cited/Vendor/`. `Proofs/WienerIkehara.lean` then imports `Mathlib.NumberTheory.LSeries.WienerIkehara`
unchanged.

### Andrews route: the `q = 1` Bailey chain

The route is the one in `Cited/Defs.lean` (docstring). A Bailey pair is taken in the multiplied form
`(1+a)_{2n} β_n = ∑_r α_r (1+a+n+r)_{n-r}/(n-r)!`. That form never divides by `(1+a)_k`, which
`Andrews_Stmt` does not assume non-zero. The only classical identity needed is terminating
Pfaff–Saalschütz in polynomial form. It is proved with a Zeilberger certificate in any commutative ring
and then transferred through `K[X]`. No Whipple, Dougall or WZ proof of the 8-fold sum is needed.

**Truth check (Lean).** The Andrews scout's complete proof (`docs/cited/AndrewsScout.lean`, 744 lines)
was re-targeted at the `Cited` definitions in an architect scratch file, now deleted. It proves
`Stmt_PPS`, `Stmt_UnitPair`, `Stmt_BaileyLemma`, `Stmt_SumChainsSucc`, `Stmt_ChainStep` and
`Stmt_BPChain` exactly as stated. With `Cited/Assembly.lean` it gives `Andrews_Stmt`. Every theorem
there has axioms `[propext, Classical.choice, Quot.sound]`, and so do `pnt_of_stmts` and
`andrews_of_stmts`.

**Truth check (numerical).** `python3 python/cited_mirror.py` runs 6340 exact checks with Lean semantics,
all passing. It covers:
* PPS over ℚ and over GF(p);
* unit pair, Bailey lemma, chain step and `BPChain`, at generic and degenerate parameters and with
  vanishing denominators;
* `Andrews_Stmt` and the assembly identity `LHS = N!(1+a)_N Bchain_N`;
* the `f = Λ` instance of `Stmt_WienerIkehara`: the Chebyshev bound, ψ(x)/x, `LSeries Λ = -ζ'/ζ` at
  s = 2, 3, 4, and `G(1⁺) = -γ` (mpmath).

A mutation test confirmed that the checks detect wrong definitions.

### Workflow for provers (Cited)

* Elaborate: `bash scripts/check.sh Zeta2Lean/Cited/Proofs/Foo.lean`.
* Build: `bash scripts/build.sh Zeta2Lean.Cited.Proofs.Foo`. For a vendored file:
  `bash scripts/build.sh Zeta2Lean.Cited.Vendor.PNT.Foo`.
* Never edit `Cited/Defs.lean`, `Cited/Statements.lean` or `Cited/Assembly.lean`. Report statement
  problems to the architect.
* Do not redeclare the proved API of `Cited/Defs.lean`.
* Put helpers in the file's own namespace (`Zeta2.Cited.PPS`, `.UnitPair`, `.Bailey`, `.ChainSum`,
  `.ChainStep`) or make them `private`. `Cited/Main.lean` imports every proof file.
* Integration, once every file is complete:
  * `bash scripts/build.sh Zeta2Lean.Cited.Main` must print
    `[propext, Classical.choice, Quot.sound]` for all three theorems.
  * Then add `import Zeta2Lean.Cited.Main` to the root `Zeta2Lean.lean` and rebuild `Zeta2Lean`.
  * Finally, drop the `grep -v '^Zeta2Lean/Cited/'` from the CI census and add the unconditional
    theorem to the CI axiom check.
