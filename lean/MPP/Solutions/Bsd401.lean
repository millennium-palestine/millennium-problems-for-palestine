import Mathlib

namespace MPP.Solutions.Bsd401

theorem main : ∀ (a p m n : ℤ), a ^ 2 ≤ 4 * p → 0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  intro a p m n h
  have h1 : 0 ≤ (2 * m - a * n) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (4 * p - a ^ 2) * n ^ 2 := mul_nonneg (sub_nonneg.mpr h) (sq_nonneg n)
  have key : 4 * (m ^ 2 - a * m * n + p * n ^ 2) = (2 * m - a * n) ^ 2 + (4 * p - a ^ 2) * n ^ 2 := by
    ring
  nlinarith

end MPP.Solutions.Bsd401
