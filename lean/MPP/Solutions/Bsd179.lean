import Mathlib

namespace MPP.Solutions.Bsd179

-- bsd-166: the Frobenius kills the Hasse derivatives of order below p
theorem frob_deriv (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] (j k : ℕ) (h : Polynomial K)
    (hkp : k < p) :
    Polynomial.hasseDeriv k (Polynomial.X ^ (p * j) * h) = Polynomial.X ^ (p * j) * Polynomial.hasseDeriv k h := by
  rcases Nat.eq_zero_or_pos k with hk | hk0
  · subst hk
    simp [Polynomial.hasseDeriv_zero]
  have hc : ∀ a : ℕ, 0 < a → a < p → (((p * j).choose a : ℕ) : K) = 0 := by
    intro a ha0 hap
    have e1 : (1 + Polynomial.X : Polynomial K) ^ (p * j) = Polynomial.expand K p ((1 + Polynomial.X) ^ j) := by
      rw [pow_mul, add_pow_char, one_pow, map_pow, map_add, map_one, Polynomial.expand_X]
    have e2 := congrArg (fun q => Polynomial.coeff q a) e1
    rw [Polynomial.coeff_one_add_X_pow, Polynomial.coeff_expand (Nat.Prime.pos hp.out),
      if_neg (Nat.not_dvd_of_pos_of_lt ha0 hap)] at e2
    exact e2
  rw [Polynomial.hasseDeriv_mul, Finset.sum_eq_single_of_mem (0, k)]
  · simp
  · simp
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have ha : ij.1 ≠ 0 := by
      intro h0
      exact hne (Prod.ext h0 (by show ij.2 = k; omega))
    have hzero : Polynomial.hasseDeriv ij.1 (Polynomial.X ^ (p * j) : Polynomial K) = 0 := by
      rw [Polynomial.X_pow_eq_monomial, Polynomial.hasseDeriv_monomial]
      simp [hc ij.1 (Nat.pos_of_ne_zero ha) (by omega)]
    rw [hzero, zero_mul]

-- bsd-178: the Leibniz identity on the level set, with cofactors from bsd-165
theorem level_id (K : Type) [Field K] (f : Polynomial K) (c : ℕ) (r : Polynomial K) (ε : K) (k : ℕ)
    (hkc : k ≤ c) :
    ∃ Q : ℕ → Polynomial K, (∀ j, j ≤ k → Polynomial.hasseDeriv j (f ^ c) = f ^ (c - j) * Q j) ∧
      ∀ x : K, (Polynomial.eval x f) ^ c = ε →
        Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k (r * f ^ c)) =
          ε * ∑ m ∈ Finset.range (k + 1), Polynomial.eval x (f ^ m * Polynomial.hasseDeriv m r * Q (k - m)) := by
  have div : ∀ c k : ℕ, k ≤ c → f ^ (c - k) ∣ Polynomial.hasseDeriv k (f ^ c) := by
    intro c
    induction c with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp
    | succ c ih =>
      intro k hk
      rcases Nat.lt_or_ge k (c + 1) with hlt | hge
      · have hkc' : k ≤ c := by omega
        rw [pow_succ', Polynomial.hasseDeriv_mul]
        apply Finset.dvd_sum
        rintro ⟨i, j⟩ hij
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
        dsimp only
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          have hj : j = k := by omega
          subst hj
          have h0 : Polynomial.hasseDeriv 0 f = f := by simp
          rw [h0]
          have hck : c + 1 - j = (c - j) + 1 := by omega
          rw [hck, pow_succ']
          exact mul_dvd_mul_left f (ih j hkc')
        · have hj : j ≤ c := by omega
          have hpow : f ^ (c + 1 - k) ∣ f ^ (c - j) := pow_dvd_pow f (by omega)
          exact dvd_mul_of_dvd_right (hpow.trans (ih j hj)) _
      · have hk' : k = c + 1 := by omega
        subst hk'
        simp
  have hQ : ∀ j : ℕ, ∃ Q : Polynomial K, j ≤ k → Polynomial.hasseDeriv j (f ^ c) = f ^ (c - j) * Q := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨Q, hq⟩ := div c j (hj.trans hkc)
      exact ⟨Q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose Q hQ using hQ
  refine ⟨Q, fun j hj => hQ j hj, ?_⟩
  intro x hx
  rw [Polynomial.hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum,
    Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hQ (k - i) (Nat.sub_le k i)]
  have hpow : f ^ k * f ^ (c - (k - i)) = f ^ i * f ^ c := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have key : f ^ k * (Polynomial.hasseDeriv i r * (f ^ (c - (k - i)) * Q (k - i))) =
      (f ^ i * Polynomial.hasseDeriv i r * Q (k - i)) * f ^ c := by
    calc f ^ k * (Polynomial.hasseDeriv i r * (f ^ (c - (k - i)) * Q (k - i)))
        = (Polynomial.hasseDeriv i r * Q (k - i)) * (f ^ k * f ^ (c - (k - i))) := by ring
      _ = (f ^ i * Polynomial.hasseDeriv i r * Q (k - i)) * f ^ c := by rw [hpow]; ring
  rw [key]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [hx]
  ring

theorem main : ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)), f ≠ 0 → ∀ (c : ℕ) (r₀ r₁ : Polynomial (ZMod p))
    (ε : ZMod p) (k j : ℕ), k < p → k ≤ c →
    ∃ Q : ℕ → Polynomial (ZMod p), (∀ i, i ≤ k → Polynomial.hasseDeriv i (f ^ c) = f ^ (c - i) * Q i) ∧
      ∀ x : ZMod p, (Polynomial.eval x f) ^ c = ε →
        Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k (Polynomial.X ^ (p * j) * (r₀ + r₁ * f ^ c))) =
          x ^ j * (Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k r₀) +
            ε * ∑ m ∈ Finset.range (k + 1), Polynomial.eval x (f ^ m * Polynomial.hasseDeriv m r₁ * Q (k - m))) := by
  intro p hp f hf c r₀ r₁ ε k j hkp hkc
  obtain ⟨Q, hQ1, hQ2⟩ := level_id (ZMod p) f c r₁ ε k hkc
  refine ⟨Q, hQ1, ?_⟩
  intro x hx
  have hfrob : Polynomial.hasseDeriv k (Polynomial.X ^ (p * j) * (r₀ + r₁ * f ^ c)) =
      Polynomial.X ^ (p * j) * (Polynomial.hasseDeriv k r₀ + Polynomial.hasseDeriv k (r₁ * f ^ c)) := by
    rw [frob_deriv p (ZMod p) j k _ hkp, map_add]
  have hxp : x ^ (p * j) = x ^ j := by
    rw [pow_mul, ZMod.pow_card]
  have expand : Polynomial.eval x (f ^ k * (Polynomial.X ^ (p * j) *
      (Polynomial.hasseDeriv k r₀ + Polynomial.hasseDeriv k (r₁ * f ^ c)))) =
      x ^ (p * j) * (Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k r₀) +
        Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k (r₁ * f ^ c))) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  rw [hfrob, expand, hxp, hQ2 x hx]

end MPP.Solutions.Bsd179
