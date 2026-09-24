import Zeta2Lean.Statements

/-!
# L2 corollary: `D_n = d_n^{12}/Φ_n` clears all denominators (proof.md §4.4; LSZ Lemma 5.4)

**Task.** Prove `Stmt_L2cor` from `Stmt_L2a`, `Stmt_L2b`, `Stmt_L2c`:
`D_n ρ₀, D_n Z₇, D_n Z₉, D_n Z₁₁ ∈ ℤ`.

**Informal proof.** `Φ_n ∣ d_n` (`Phi_dvd_dn` in `Defs.lean`) and `D_n Φ_n = d_n^{12}`
(`Dn_mul_Phi`).
* `Z`'s: by L2a, `d_n^{8-i} c_i = ∑_k d_n^{8-i} r_{i,k} ∈ ℤ`.  `D_n = d_n^{8-i} · (d_n^{4+i}/Φ_n)` and
  `Φ_n ∣ d_n ∣ d_n^{4+i}`, so `D_n c_i ∈ ℤ` for `i = 3, 5, 7`; multiply by `46080`, `860160`,
  `10321920`.
* `ρ₀`: show `v_q(D_n ρ₀) ≥ 0` for every prime `q` (or `ρ₀ = 0`).  If `q ∣ Φ_n`, i.e.
  `q ≤ n`, `q ≥ 11`, `q² > 2n`: then `v_q(d_n) = ⌊log_q n⌋ = 1` (`q ≤ n < q²`), `v_q(Φ_n) = 1`, so
  `v_q(D_n) = 12 - 1 = 11`, and `v_q(ρ₀) ≥ -11` (L2c).  Otherwise `v_q(D_n) = 12 v_q(d_n)` and
  `v_q(d_n^{12} ρ₀) ≥ 0` (L2b).  A rational with non-negative valuation at every prime is an integer.

**Formal route taken here.** For `ρ₀` we avoid valuations of `D_n` altogether: L2b gives an
integer `z = d_n^{12} ρ₀`; every prime `p ∣ Φ_n` divides `z` because
`v_p(z) = 12 v_p(d_n) + v_p(ρ₀) ≥ 12 - 11 = 1` (`v_p(d_n) = log_p n = 1` by
`Nat.factorization_lcmUpto`, and L2c); `Φ_n` is a product of distinct primes, so `Φ_n ∣ z`
(`Finset.prod_primes_dvd`); finally `D_n ρ₀ = z / Φ_n` by `Dn_mul_Phi`.

**Numerical check.** `python/mirror.py`, section "... Stmt_L2cor" (`n ≤ 60`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2

/-- A finite sum of rationals each of which is an integer is an integer. -/
private theorem L2cor_sum_isInt {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ k ∈ s, ∃ z : ℤ, f k = z) : ∃ z : ℤ, ∑ k ∈ s, f k = z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z₁, hz₁⟩ := h a (mem_insert_self a s)
    obtain ⟨z₂, hz₂⟩ := ih (fun k hk => h k (mem_insert_of_mem hk))
    exact ⟨z₁ + z₂, by rw [sum_insert ha, hz₁, hz₂]; push_cast; ring⟩

/-- `d_n^{8-i} c_i ∈ ℤ` (L2a summed over `k`). -/
private theorem L2cor_csum_isInt (h2a : Stmt_L2a) (n i : ℕ) (hi1 : 1 ≤ i) (hi8 : i ≤ 8) :
    ∃ z : ℤ, (dn n : ℚ) ^ (8 - i) * csum n i = z := by
  unfold csum
  rw [Finset.mul_sum]
  exact L2cor_sum_isInt _ _ fun k hk =>
    h2a n i k hi1 hi8 (Nat.lt_succ_iff.mp (mem_range.mp hk))

/-- `D_n = d_n^{8-i} · (d_n^{4+i} / Φ_n)` in `ℕ` (for `i ≤ 8`). -/
private theorem L2cor_Dn_split (n i : ℕ) (hi : i ≤ 8) :
    Dn n = dn n ^ (8 - i) * (dn n ^ (4 + i) / Phi n) := by
  have hdvd : Phi n ∣ dn n ^ (4 + i) := (Phi_dvd_dn n).trans (dvd_pow_self _ (by omega))
  rw [← Nat.mul_div_assoc _ hdvd, ← pow_add, show 8 - i + (4 + i) = 12 by omega]
  rfl

/-- `D_n · (c · c_i) ∈ ℤ` for every integer `c` and `1 ≤ i ≤ 8`. -/
private theorem L2cor_Z_isInt (h2a : Stmt_L2a) (n i : ℕ) (hi1 : 1 ≤ i) (hi8 : i ≤ 8) (c : ℤ) :
    ∃ z : ℤ, (Dn n : ℚ) * ((c : ℚ) * csum n i) = z := by
  obtain ⟨w, hw⟩ := L2cor_csum_isInt h2a n i hi1 hi8
  rw [L2cor_Dn_split n i hi8]
  generalize dn n ^ (4 + i) / Phi n = e
  refine ⟨c * (e : ℤ) * w, ?_⟩
  push_cast
  rw [← hw]
  ring

/-- `v_p(d_n) = 1` for a prime `p` with `p ≤ n < p²`. -/
private theorem L2cor_factorization_dn {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) (hn : n < p ^ 2) :
    (dn n).factorization p = 1 := by
  unfold dn
  rw [Nat.factorization_lcmUpto n hp, Nat.log_eq_iff (Or.inl one_ne_zero)]
  exact ⟨by simpa using hpn, by simpa using hn⟩

/-- Every prime factor `p` of `Φ_n` divides the integer `z = d_n^{12} ρ₀` (via L2c). -/
private theorem L2cor_prime_dvd (h2c : Stmt_L2c) {n p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hpn : p ≤ n) (hn : 2 * n < p ^ 2) (z : ℤ) (hz : (dn n : ℚ) ^ 12 * rho0 n = z) :
    (p : ℤ) ∣ z := by
  have := Fact.mk hp
  by_cases hz0 : z = 0
  · rw [hz0]; exact dvd_zero _
  have hrho : rho0 n ≠ 0 := by
    intro h
    apply hz0
    have : ((z : ℤ) : ℚ) = 0 := by rw [← hz, h, mul_zero]
    exact_mod_cast this
  have hd : (dn n : ℚ) ≠ 0 := by exact_mod_cast (Nat.lcmUpto_pos n).ne'
  have hv1 : padicValNat p (dn n) = 1 := by
    rw [← Nat.factorization_def _ hp]
    exact L2cor_factorization_dn hp hpn (by omega)
  have hval : padicValRat p (z : ℚ) = 12 * (padicValNat p (dn n) : ℤ) + padicValRat p (rho0 n) := by
    rw [← hz, padicValRat.mul (pow_ne_zero _ hd) hrho, padicValRat.pow, padicValRat.of_nat]
    push_cast
    ring
  have hc := h2c n p hp hp11 hn
  rw [padicValRat.of_int, hv1] at hval
  have h1 : 1 ≤ padicValInt p z := by omega
  have := (padicValInt_dvd_iff 1 z).mpr (Or.inr h1)
  simpa using this

/-- `Φ_n ∣ z` for the integer `z = d_n^{12} ρ₀`. -/
private theorem L2cor_Phi_dvd (h2c : Stmt_L2c) (n : ℕ) (z : ℤ)
    (hz : (dn n : ℚ) ^ 12 * rho0 n = z) : (Phi n : ℤ) ∣ z := by
  rw [Int.natCast_dvd]
  unfold Phi
  apply Finset.prod_primes_dvd
  · intro p hp
    simp only [Finset.mem_filter] at hp
    exact hp.2.1.prime
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpn, hp, hp11, hpn2⟩ := hp
    rw [← Int.natCast_dvd]
    exact L2cor_prime_dvd h2c hp hp11 (by omega) hpn2 z hz

/-- `D_n ρ₀ ∈ ℤ`. -/
private theorem L2cor_rho0_isInt (h2b : Stmt_L2b) (h2c : Stmt_L2c) (n : ℕ) :
    ∃ z : ℤ, (Dn n : ℚ) * rho0 n = z := by
  obtain ⟨z, hz⟩ := h2b n
  obtain ⟨w, hw⟩ := L2cor_Phi_dvd h2c n z hz
  refine ⟨w, ?_⟩
  have hPhi : (Phi n : ℚ) ≠ 0 := by exact_mod_cast (Phi_pos n).ne'
  have hmul : (Dn n : ℚ) * (Phi n : ℚ) = (dn n : ℚ) ^ 12 := by exact_mod_cast Dn_mul_Phi n
  have hw' : (z : ℚ) = (Phi n : ℚ) * w := by rw [hw]; push_cast; ring
  apply mul_right_cancel₀ hPhi
  calc (Dn n : ℚ) * rho0 n * Phi n = ((Dn n : ℚ) * Phi n) * rho0 n := by ring
    _ = (Phi n : ℚ) * w := by rw [hmul, hz, hw']
    _ = (w : ℚ) * Phi n := by ring

theorem L2cor_proof (h2a : Stmt_L2a) (h2b : Stmt_L2b) (h2c : Stmt_L2c) : Stmt_L2cor := by
  intro n
  obtain ⟨a0, ha0⟩ := L2cor_rho0_isInt h2b h2c n
  obtain ⟨a1, ha1⟩ := L2cor_Z_isInt h2a n 3 (by norm_num) (by norm_num) 46080
  obtain ⟨a2, ha2⟩ := L2cor_Z_isInt h2a n 5 (by norm_num) (by norm_num) 860160
  obtain ⟨a3, ha3⟩ := L2cor_Z_isInt h2a n 7 (by norm_num) (by norm_num) 10321920
  refine ⟨![a0, a1, a2, a3], ?_, ?_, ?_, ?_⟩
  · simpa using ha0
  · simpa [Z7] using ha1
  · simpa [Z9] using ha2
  · simpa [Z11] using ha3

end Zeta2

end
