import Mathlib

namespace MPP.Solutions.Bsd291

theorem main : ∀ (p : ℕ) (a : ℤ), a ^ 2 ≤ 4 * (p : ℤ) →
    ∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + (p : ℤ) * n ^ 2 := by
  intro p a h m n
  nlinarith [sq_nonneg (2 * m - a * n), mul_nonneg (sub_nonneg.2 h) (sq_nonneg n)]

end MPP.Solutions.Bsd291
