import Mathlib

namespace MPP.Solutions.Bsd162

theorem main : ∀ f : ℕ → ℝ, (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) → f 1 = 1 →
    (∀ p k : ℕ, p.Prime → |f (p ^ k)| ≤ ((k : ℝ) + 1) * Real.sqrt ((p ^ k : ℕ) : ℝ)) →
    ∀ n : ℕ, 0 < n → |f n| ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
  intro f hmul h1 hpp
  have key : ∀ n : ℕ, 0 < n → |f n| ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp _ =>
      intro _
      have h := hpp p k hp
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
      push_cast at h ⊢
      exact h
    | zero =>
      intro h
      exact absurd h (lt_irrefl 0)
    | one =>
      intro _
      rw [h1]
      simp
    | coprime a b ha hb hab iha ihb =>
      intro _
      rw [hmul a b hab, abs_mul, Nat.Coprime.card_divisors_mul hab, Nat.cast_mul,
        Nat.cast_mul a b, Real.sqrt_mul (Nat.cast_nonneg a)]
      have h := mul_le_mul (iha (by omega)) (ihb (by omega)) (abs_nonneg _) (by positivity)
      calc |f a| * |f b| ≤ _ := h
        _ = _ := by ring
  exact key

end MPP.Solutions.Bsd162
