import Mathlib

namespace MPP.Solutions.Bsd166

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (j k : ℕ) (h : Polynomial K),
    0 < k → k < p →
    Polynomial.hasseDeriv k (Polynomial.X ^ (p * j) * h) = Polynomial.X ^ (p * j) * Polynomial.hasseDeriv k h := by
  intro p hp K _ _ j k h hk0 hkp
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

end MPP.Solutions.Bsd166
