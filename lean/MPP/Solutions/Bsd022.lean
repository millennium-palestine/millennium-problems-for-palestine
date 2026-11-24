import Mathlib

namespace MPP.Solutions.Bsd022

theorem main : ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n →
    ((m * n).divisors.card : ℝ) * Real.sqrt ((m * n : ℕ) : ℝ) =
      ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ)) * ((n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) := by
  intro m n hm hn hmn
  rw [Nat.Coprime.card_divisors_mul hmn]
  have hm' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  push_cast
  rw [Real.sqrt_mul hm']
  ring

end MPP.Solutions.Bsd022
