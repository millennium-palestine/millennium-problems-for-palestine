import Mathlib

namespace MPP.Solutions.Bsd165

theorem main : ∀ (K : Type) [Field K] (f : Polynomial K), f ≠ 0 → ∀ c k : ℕ, k ≤ c →
    ∃ Q : Polynomial K, Polynomial.hasseDeriv k (f ^ c) = f ^ (c - k) * Q ∧ Q.natDegree ≤ k * f.natDegree := by
  intro K _ f hf c k hkc
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
  obtain ⟨Q, hQ⟩ := div c k hkc
  refine ⟨Q, hQ, ?_⟩
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  · have hdeg1 : (f ^ (c - k) * Q).natDegree = (c - k) * f.natDegree + Q.natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero _ hf) hQ0, Polynomial.natDegree_pow]
    have hdeg2 : (Polynomial.hasseDeriv k (f ^ c)).natDegree ≤ c * f.natDegree - k := by
      have := Polynomial.natDegree_hasseDeriv_le (f ^ c) k
      rwa [Polynomial.natDegree_pow] at this
    rw [hQ, hdeg1] at hdeg2
    have hc : c * f.natDegree = (c - k) * f.natDegree + k * f.natDegree := by
      rw [← add_mul, Nat.sub_add_cancel hkc]
    generalize (c - k) * f.natDegree = A at hdeg2 hc
    generalize k * f.natDegree = C at hdeg2 hc ⊢
    generalize c * f.natDegree = B at hdeg2 hc
    omega

end MPP.Solutions.Bsd165
