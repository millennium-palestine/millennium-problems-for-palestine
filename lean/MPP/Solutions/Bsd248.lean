import Mathlib

namespace MPP.Solutions.Bsd248

theorem main : ∀ (K : Type) [Field K] (p J N : ℕ) (r : Fin J → Polynomial K), 0 < p → N ≤ p →
    (∀ i, (r i).natDegree < N) →
    ∀ (j : Fin J) (t : ℕ), t < N →
      (∑ i : Fin J, (Polynomial.X : Polynomial K) ^ (p * (i : ℕ)) * r i).coeff (p * (j : ℕ) + t) = (r j).coeff t := by
  intro K _ p J N r hp hN hdeg j t ht
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_X_pow_mul', if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  · intro i _ hij
    rw [Polynomial.coeff_X_pow_mul']
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : p * ((i : ℕ) + 1) ≤ p * (j : ℕ) := Nat.mul_le_mul_left p hlt
      have h2 : p * ((i : ℕ) + 1) = p * (i : ℕ) + p := by ring
      by_cases h : p * (i : ℕ) ≤ p * (j : ℕ) + t
      · rw [if_pos h]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have := hdeg i
        omega
      · rw [if_neg h]
    · have h1 : p * ((j : ℕ) + 1) ≤ p * (i : ℕ) := Nat.mul_le_mul_left p hgt
      have h2 : p * ((j : ℕ) + 1) = p * (j : ℕ) + p := by ring
      have h3 : ¬ (p * (i : ℕ) ≤ p * (j : ℕ) + t) := by omega
      rw [if_neg h3]
  · intro h
    exact absurd (Finset.mem_univ j) h

end MPP.Solutions.Bsd248
