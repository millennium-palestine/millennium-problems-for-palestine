import Mathlib

namespace MPP.Solutions.Bsd255

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K J : ℕ) (r : Fin J → Polynomial (ZMod p)),
    (∀ j, (r j).natDegree < K) →
    ∀ u : ℕ, K ≤ u % p →
      (∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r j).coeff u = 0 := by
  intro p _ K J r hr u hu
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hm : (u - p * (j : ℕ)) % p = u % p := by
      rw [← Nat.add_mul_mod_self_left (u - p * (j : ℕ)) p (j : ℕ), Nat.sub_add_cancel h]
    have h1 : K ≤ u - p * (j : ℕ) := le_trans hu (by rw [← hm]; exact Nat.mod_le _ _)
    exact lt_of_lt_of_le (hr j) h1
  · rfl

end MPP.Solutions.Bsd255
