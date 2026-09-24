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
the proof files are complete. At present it also shows `sorryAx`, which comes from the stubs.

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
Zeta2Lean/Proofs/*.lean    theorem X_proof (deps as hypotheses) : Stmt_X := by sorry   (24 files)
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
