import Mathlib

namespace MPP.Solutions.Bsd341

theorem main : ∀ (a p m n : ℤ), 0 < p → a ^ 2 ≤ 4 * p → 0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  intro a p m n hp ha
  have hd : 0 ≤ 4 * p - a ^ 2 := by linarith
  have e : 4 * p * (m ^ 2 - a * m * n + p * n ^ 2)
      = (2 * p * n - a * m) ^ 2 + (4 * p - a ^ 2) * m ^ 2 := by ring
  have h : 0 ≤ 4 * p * (m ^ 2 - a * m * n + p * n ^ 2) := by
    rw [e]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hd (sq_nonneg m))
  nlinarith [h, hp]

end MPP.Solutions.Bsd341
