import Mathlib

namespace MPP.Solutions.Bsd262

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K J : ℕ) (g : Polynomial (ZMod p)) (r₀ r₁ : Fin J → Polynomial (ZMod p)),
    (∀ j, (r₀ j).natDegree < K) → (∀ j, (r₁ j).natDegree < K) →
    ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * (r₀ j + r₁ j * g) = 0 →
    ∀ u : ℕ, K ≤ u % p →
      (g * ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₁ j).coeff u = 0 := by
  intro p _ K J g r₀ r₁ h0 _ hsum u hu
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hA : ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₀ j +
      g * ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₁ j =
      ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * (r₀ j + r₁ j * g) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum] at hA
  have hAc : (∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₀ j).coeff u = 0 := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    rw [Polynomial.coeff_X_pow_mul']
    by_cases hpj : p * (j : ℕ) ≤ u
    · rw [if_pos hpj]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hdm := Nat.div_add_mod u p
      have hjq : (j : ℕ) ≤ u / p := (Nat.le_div_iff_mul_le hp).mpr (by linarith [hpj])
      have h3 : p * (j : ℕ) ≤ p * (u / p) := Nat.mul_le_mul_left p hjq
      have hd := h0 j
      omega
    · rw [if_neg hpj]
  have h := congrArg (fun q => Polynomial.coeff q u) hA
  simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at h
  rw [hAc, zero_add] at h
  exact h

end MPP.Solutions.Bsd262
