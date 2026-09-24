import Zeta2Lean.Statements

/-!
# Closed form of `F_J(0)` (proof.md §4.3 Step 4)

**Task.** Prove `Stmt_FJClosed : constantCoeff (Fser n ℓ J) = FJ0 n ℓ J` for `1 ≤ ℓ ≤ n`,
`J ∈ chains 8 (n-ℓ)`.  No hypotheses.

**Informal proof.** `constantCoeff` is a ring hom, `constantCoeff (φ⁻¹) = (constantCoeff φ)⁻¹`,
`constantCoeff (psPoch c d k) = rpoch c k`.  So `F_J(0)` is the product of the constant terms:
  `F_J(0) = -(N+1) ℓ P_ℓ(0) ∏_{i=1}^{8} (1/2)_{d_i}/d_i!
          · ∏_{i=1}^{7} (-N)_{J_i}(ℓ+1/2)_{J_i}/((ℓ+1)_{J_i}(1/2-N)_{J_i})
          · (ℓ+1)_{J_8} (-N)_{J_8} / ((J_8+1)(ℓ+1)_{J_8}(1/2-N)_{J_8})`,
  `P_ℓ(0) = 2^{16n} (ℓ-1/2)^3 (1/2)_{ℓ-1}^8 (1/2)_N^8 / (ℓ!^8 N!^8)`.
Use (all for natural numbers, `J ≤ N`):
* `(1/2)_m / m! = C(2m,m) / 4^m`;  `(1/2)_{ℓ-1}/ℓ! = C(2ℓ-2,ℓ-1) / (4^{ℓ-1} ℓ)`;
* `(-N)_J (ℓ+1/2)_J / ((ℓ+1)_J (1/2-N)_J) = C(2(ℓ+J),ℓ+J) C(2(N-J),N-J) / (C(2ℓ,ℓ) C(2N,N))`;
* `(-N)_J / ((J+1)(1/2-N)_J) = 4^J C(2(N-J),N-J) / ((J+1) C(2N,N))`  (and `(ℓ+1)_{J_8}` cancels).
Then all powers of 2 collapse (`∑ d_i = J_8`, `2^{16n} = 4^{8ℓ} 4^{8N}`) and one obtains
  `F_J(0) = -64 (2ℓ-1)^{-4} C(2ℓ-2,ℓ-1) (N+1)/(J_8+1) ∏_{i≤8} C(2d_i,d_i)
           ∏_{i≤7} C(2(ℓ+J_i),ℓ+J_i) ∏_{i≤8} C(2(N-J_i),N-J_i)`  (= `FJ0`).

**Formal proof (this file, complete).**
* `fjc_cc_psPoch`: `constantCoeff (psPoch c d k) = rpoch c k`.
* Pochhammer calculus in any commutative ring: `fjc_rpoch_succ`, `fjc_rpoch_succ'`,
  `fjc_rpoch_add` (`(x)_{a+b} = (x)_a (x+a)_b`) and the reflection
  `fjc_rpoch_reflect : (-y-J+1)_J = (-1)^J (y)_J`.
* Over `ℚ`: `(1)_k = k!`, `(1/2)_m 4^m = C(2m,m) m!` (induction with
  `Nat.succ_mul_centralBinom_succ`), `(a+1)_k = (a+k)!/a!`, `(a+1/2)_k` in closed form.
* The three factor identities `fjc_factorA/B/C` (after writing `N = M + J`, the reflection turns
  `(-N)_J` into `(-1)^J (M+1)_J` and `(1/2-N)_J` into `(-1)^J (M+1/2)_J`).
* `fjc_sum_d`: `∑_{i<8} (J_i - J_{i-1}) = J_8` along a chain.
* Main proof: substitute `n = ℓ + N`, `ℓ = ℓ' + 1`; push `constantCoeff` through `Fser`; rewrite the
  three products and the `P_ℓ(0)` part; `C(2ℓ'+2, ℓ'+1) = 2(2ℓ'+1) C(2ℓ',ℓ')/(ℓ'+1)`,
  `2^{16n} = 4^{8n}`; then `field_simp; ring` with the three remaining products as atoms.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2

/-! ### Pochhammer calculus -/

private lemma fjc_cc_psPoch (c d : ℚ) (k : ℕ) : constantCoeff (psPoch c d k) = rpoch c k := by
  unfold psPoch rpoch
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

private lemma fjc_rpoch_succ {K : Type*} [CommRing K] (x : K) (k : ℕ) :
    rpoch x (k + 1) = rpoch x k * (x + k) := by
  unfold rpoch
  rw [Finset.prod_range_succ]

private lemma fjc_rpoch_succ' {K : Type*} [CommRing K] (x : K) (k : ℕ) :
    rpoch x (k + 1) = x * rpoch (x + 1) k := by
  unfold rpoch
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring

private lemma fjc_rpoch_add {K : Type*} [CommRing K] (x : K) (a b : ℕ) :
    rpoch x (a + b) = rpoch x a * rpoch (x + a) b := by
  unfold rpoch
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  ring

/-- Reflection: `(-y-J+1)_J = (-1)^J (y)_J`. -/
private lemma fjc_rpoch_reflect {K : Type*} [CommRing K] (y : K) (J : ℕ) :
    rpoch (-y - J + 1) J = (-1) ^ J * rpoch y J := by
  induction J with
  | zero => simp [rpoch]
  | succ J ih =>
    rw [fjc_rpoch_succ', fjc_rpoch_succ y J]
    have h : -y - ((J + 1 : ℕ) : K) + 1 + 1 = -y - J + 1 := by push_cast; ring
    rw [h, ih]
    push_cast
    ring

private lemma fjc_rpoch_one (k : ℕ) : rpoch (1 : ℚ) k = (k.factorial : ℚ) := by
  induction k with
  | zero => simp [rpoch]
  | succ k ih =>
    rw [fjc_rpoch_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- `(1/2)_m 4^m = C(2m,m) m!`. -/
private lemma fjc_rpoch_half (m : ℕ) :
    rpoch (1 / 2 : ℚ) m * 4 ^ m = ((Nat.choose (2 * m) m : ℕ) : ℚ) * (m.factorial : ℚ) := by
  induction m with
  | zero => simp [rpoch]
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
    have h' : ((m : ℚ) + 1) * ((Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) =
        2 * (2 * m + 1) * ((Nat.choose (2 * m) m : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [fjc_rpoch_succ, pow_succ, Nat.factorial_succ]
    push_cast
    linear_combination (4 * (1 / 2 + (m : ℚ))) * ih - (m.factorial : ℚ) * h'

private lemma fjc_choose_pos (m : ℕ) : (0 : ℚ) < ((Nat.choose (2 * m) m : ℕ) : ℚ) := by
  exact_mod_cast Nat.centralBinom_pos m

private lemma fjc_rpoch_nat_add_one (a k : ℕ) :
    rpoch ((a : ℚ) + 1) k = ((a + k).factorial : ℚ) / (a.factorial : ℚ) := by
  have h := fjc_rpoch_add (1 : ℚ) a k
  rw [show (1 : ℚ) + a = a + 1 by ring, fjc_rpoch_one, fjc_rpoch_one] at h
  rw [eq_div_iff (by positivity), h]
  ring

private lemma fjc_rpoch_nat_add_half (a k : ℕ) :
    rpoch ((a : ℚ) + 1 / 2) k =
      ((Nat.choose (2 * (a + k)) (a + k) : ℕ) : ℚ) * ((a + k).factorial : ℚ) * 4 ^ a /
        (((Nat.choose (2 * a) a : ℕ) : ℚ) * (a.factorial : ℚ) * 4 ^ (a + k)) := by
  have h := fjc_rpoch_add (1 / 2 : ℚ) a k
  rw [show (1 / 2 : ℚ) + a = a + 1 / 2 by ring] at h
  have h1 := fjc_rpoch_half a
  have h2 := fjc_rpoch_half (a + k)
  have hc := fjc_choose_pos a
  rw [eq_div_iff (by positivity), ← h1, ← h2, h]
  ring

private lemma fjc_rpoch_half' (m : ℕ) :
    rpoch (1 / 2 : ℚ) m = ((Nat.choose (2 * m) m : ℕ) : ℚ) * (m.factorial : ℚ) / 4 ^ m := by
  rw [eq_div_iff (by positivity)]
  exact fjc_rpoch_half m

/-! ### The three factor identities -/

/-- `(1/2)_d / d! = C(2d,d) / 4^d`. -/
private lemma fjc_factorA (d : ℕ) :
    rpoch (1 / 2 : ℚ) d / (d.factorial : ℚ) = ((Nat.choose (2 * d) d : ℕ) : ℚ) / 4 ^ d := by
  rw [div_eq_div_iff (by positivity) (by positivity)]
  exact fjc_rpoch_half d

/-- `(-N)_J (a+1/2)_J / ((a+1)_J (1/2-N)_J) = C(2(a+J),a+J) C(2(N-J),N-J) / (C(2a,a) C(2N,N))`. -/
private lemma fjc_factorB (a N J : ℕ) (hJ : J ≤ N) :
    rpoch (-(N : ℚ)) J * rpoch ((a : ℚ) + 1 / 2) J *
        (rpoch ((a : ℚ) + 1) J * rpoch (1 / 2 - (N : ℚ)) J)⁻¹ =
      ((Nat.choose (2 * (a + J)) (a + J) : ℕ) : ℚ) *
          ((Nat.choose (2 * (N - J)) (N - J) : ℕ) : ℚ) /
        (((Nat.choose (2 * a) a : ℕ) : ℚ) * ((Nat.choose (2 * N) N : ℕ) : ℚ)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + J := ⟨N - J, by omega⟩
  rw [Nat.add_sub_cancel]
  have e1 : rpoch (-((M + J : ℕ) : ℚ)) J = (-1) ^ J * rpoch ((M : ℚ) + 1) J := by
    rw [← fjc_rpoch_reflect]; congr 1; push_cast; ring
  have e2 : rpoch (1 / 2 - ((M + J : ℕ) : ℚ)) J = (-1) ^ J * rpoch ((M : ℚ) + 1 / 2) J := by
    rw [← fjc_rpoch_reflect]; congr 1; push_cast; ring
  rw [e1, e2, fjc_rpoch_nat_add_one, fjc_rpoch_nat_add_one, fjc_rpoch_nat_add_half,
    fjc_rpoch_nat_add_half]
  have h1 := fjc_choose_pos a
  have h2 := fjc_choose_pos M
  have h3 := fjc_choose_pos (a + J)
  have h4 := fjc_choose_pos (M + J)
  have hs : ((-1 : ℚ)) ^ J ≠ 0 := pow_ne_zero _ (by norm_num)
  have f1 : ((a.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : ((M.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((a + J).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((M + J).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- `(a+1)_J (-N)_J / ((J+1)(a+1)_J (1/2-N)_J) = 4^J C(2(N-J),N-J) / ((J+1) C(2N,N))`. -/
private lemma fjc_factorC (a N J : ℕ) (hJ : J ≤ N) :
    rpoch ((a : ℚ) + 1) J * rpoch (-(N : ℚ)) J *
        (((J : ℚ) + 1) * rpoch ((a : ℚ) + 1) J * rpoch (1 / 2 - (N : ℚ)) J)⁻¹ =
      4 ^ J * ((Nat.choose (2 * (N - J)) (N - J) : ℕ) : ℚ) /
        (((J : ℚ) + 1) * ((Nat.choose (2 * N) N : ℕ) : ℚ)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + J := ⟨N - J, by omega⟩
  rw [Nat.add_sub_cancel]
  have e1 : rpoch (-((M + J : ℕ) : ℚ)) J = (-1) ^ J * rpoch ((M : ℚ) + 1) J := by
    rw [← fjc_rpoch_reflect]; congr 1; push_cast; ring
  have e2 : rpoch (1 / 2 - ((M + J : ℕ) : ℚ)) J = (-1) ^ J * rpoch ((M : ℚ) + 1 / 2) J := by
    rw [← fjc_rpoch_reflect]; congr 1; push_cast; ring
  rw [e1, e2, fjc_rpoch_nat_add_one, fjc_rpoch_nat_add_one, fjc_rpoch_nat_add_half]
  have h2 := fjc_choose_pos M
  have h4 := fjc_choose_pos (M + J)
  have hs : ((-1 : ℚ)) ^ J ≠ 0 := pow_ne_zero _ (by norm_num)
  have f1 : ((a.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : ((M.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f3 : (((a + J).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f4 : (((M + J).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hJ1 : ((J : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Chains of length 8 -/

/-- Telescoping along a chain: `∑_{i<8} (J_i - J_{i-1}) = J_8`. -/
private lemma fjc_sum_d (ch : Fin 8 → ℕ) (hmono : ∀ a b : Fin 8, a ≤ b → ch a ≤ ch b) :
    ∑ i : Fin 8, (ch i - chainPrev ch i) = ch 7 := by
  rw [Fin.sum_univ_eight]
  have c0 : chainPrev ch 0 = 0 := rfl
  have c1 : chainPrev ch 1 = ch 0 := rfl
  have c2 : chainPrev ch 2 = ch 1 := rfl
  have c3 : chainPrev ch 3 = ch 2 := rfl
  have c4 : chainPrev ch 4 = ch 3 := rfl
  have c5 : chainPrev ch 5 = ch 4 := rfl
  have c6 : chainPrev ch 6 = ch 5 := rfl
  have c7 : chainPrev ch 7 = ch 6 := rfl
  have h01 := hmono 0 1 (by decide)
  have h12 := hmono 1 2 (by decide)
  have h23 := hmono 2 3 (by decide)
  have h34 := hmono 3 4 (by decide)
  have h45 := hmono 4 5 (by decide)
  have h56 := hmono 5 6 (by decide)
  have h67 := hmono 6 7 (by decide)
  rw [c0, c1, c2, c3, c4, c5, c6, c7]
  omega

/-! ### The closed form -/

theorem FJClosed_proof : Stmt_FJClosed := by
  intro n l ch hl hln hch
  obtain ⟨N, rfl⟩ : ∃ N, n = l + N := ⟨n - l, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hNsub : l + 1 + N - (l + 1) = N := by omega
  rw [hNsub] at hch
  have hmem := mem_chains.1 hch
  -- push `constantCoeff` through the definition of `F_J`
  simp only [Fser, Pser, FJ0, hNsub, Nat.add_sub_cancel, map_mul, map_sub, map_prod, map_pow,
    constantCoeff_inv, constantCoeff_C, constantCoeff_X, fjc_cc_psPoch, mul_zero, sub_zero]
  -- the three products
  have hA : ∏ x : Fin 8, rpoch (1 / 2 : ℚ) (ch x - chainPrev ch x) /
        ((ch x - chainPrev ch x).factorial : ℚ) =
      (∏ x : Fin 8,
          ((Nat.choose (2 * (ch x - chainPrev ch x)) (ch x - chainPrev ch x) : ℕ) : ℚ)) /
        4 ^ (ch 7) := by
    rw [Finset.prod_congr rfl (fun (x : Fin 8) _ => fjc_factorA (ch x - chainPrev ch x)),
      Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, fjc_sum_d ch hmem.2]
  have hB : ∏ x : Fin 7, (rpoch (-(N : ℚ)) (ch x.castSucc) *
          rpoch (((l + 1 : ℕ) : ℚ) + 1 / 2) (ch x.castSucc) *
          (rpoch (((l + 1 : ℕ) : ℚ) + 1) (ch x.castSucc) *
            rpoch (1 / 2 - (N : ℚ)) (ch x.castSucc))⁻¹) =
      (∏ x : Fin 7,
          ((Nat.choose (2 * (l + 1 + ch x.castSucc)) (l + 1 + ch x.castSucc) : ℕ) : ℚ)) *
        (∏ x : Fin 7, ((Nat.choose (2 * (N - ch x.castSucc)) (N - ch x.castSucc) : ℕ) : ℚ)) /
        (((Nat.choose (2 * (l + 1)) (l + 1) : ℕ) : ℚ) *
          ((Nat.choose (2 * N) N : ℕ) : ℚ)) ^ 7 := by
    rw [Finset.prod_congr rfl
        (fun (x : Fin 7) _ => fjc_factorB (l + 1) N (ch x.castSucc) (hmem.1 _)),
      Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hC := fjc_factorC (l + 1) N (ch 7) (hmem.1 7)
  have hD : ∏ x : Fin 8, ((Nat.choose (2 * (N - ch x)) (N - ch x) : ℕ) : ℚ) =
      (∏ x : Fin 7, ((Nat.choose (2 * (N - ch x.castSucc)) (N - ch x.castSucc) : ℕ) : ℚ)) *
        ((Nat.choose (2 * (N - ch 7)) (N - ch 7) : ℕ) : ℚ) := by
    rw [Fin.prod_univ_castSucc]
    rfl
  rw [hA, hB, hC, hD]
  -- the `P_ℓ(0)` part
  simp only [fjc_rpoch_one, fjc_rpoch_half']
  rw [show 2 * (l + 1) - 2 = 2 * l by omega, Nat.factorial_succ]
  have hcb : ((Nat.choose (2 * (l + 1)) (l + 1) : ℕ) : ℚ) =
      2 * (2 * l + 1) * ((Nat.choose (2 * l) l : ℕ) : ℚ) / (l + 1) := by
    have h := Nat.succ_mul_centralBinom_succ l
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
    have h' : ((l : ℚ) + 1) * ((Nat.choose (2 * (l + 1)) (l + 1) : ℕ) : ℚ) =
        2 * (2 * l + 1) * ((Nat.choose (2 * l) l : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [eq_div_iff (by positivity), ← h']
    ring
  have h2pow : (2 : ℚ) ^ (16 * (l + 1 + N)) = 4 ^ (8 * (l + 1 + N)) := by
    rw [pow_mul, pow_mul]
    norm_num
  rw [hcb, h2pow]
  -- the remaining products are atoms
  generalize (∏ x : Fin 8,
    ((Nat.choose (2 * (ch x - chainPrev ch x)) (ch x - chainPrev ch x) : ℕ) : ℚ)) = X1
  generalize (∏ x : Fin 7,
    ((Nat.choose (2 * (l + 1 + ch x.castSucc)) (l + 1 + ch x.castSucc) : ℕ) : ℚ)) = X2
  generalize (∏ x : Fin 7,
    ((Nat.choose (2 * (N - ch x.castSucc)) (N - ch x.castSucc) : ℕ) : ℚ)) = X3
  have c1 := fjc_choose_pos l
  have c2 := fjc_choose_pos N
  have f1 : ((l.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have f2 : ((N.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  have hl1 : ((l : ℚ) + 1) ≠ 0 := by positivity
  have hl2 : (2 * (l : ℚ) + 1) ≠ 0 := by positivity
  have hj : ((ch 7 : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  have hl3 : (2 * ((l : ℚ) + 1) - 1) = 2 * (l : ℚ) + 1 := by ring
  rw [hl3]
  field_simp
  ring

end Zeta2

end
