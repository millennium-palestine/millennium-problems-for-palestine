import Mathlib

namespace MPP.Solutions.Bsd178

theorem main : ∀ (K : Type) [Field K] (f : Polynomial K), f ≠ 0 → ∀ (c : ℕ) (r : Polynomial K) (ε : K) (k : ℕ), k ≤ c →
    ∃ Q : ℕ → Polynomial K, (∀ j, j ≤ k → Polynomial.hasseDeriv j (f ^ c) = f ^ (c - j) * Q j) ∧
      ∀ x : K, (Polynomial.eval x f) ^ c = ε →
        Polynomial.eval x (f ^ k * Polynomial.hasseDeriv k (r * f ^ c)) =
          ε * ∑ m ∈ Finset.range (k + 1), Polynomial.eval x (f ^ m * Polynomial.hasseDeriv m r * Q (k - m)) := by
  intro K _ f _ c r ε k hkc
  -- divisibility of the Hasse derivatives of a power, as in bsd-165
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
  -- one cofactor for each order j, chosen uniformly; only j ≤ k is used
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

end MPP.Solutions.Bsd178
