import Mathlib

namespace MPP.Solutions.Bsd158

/-- Four times the form is a square plus `(4p − a²) n²`, and both terms are nonnegative under the
hypothesis `a² ≤ 4p`. -/
theorem main : ∀ (a p m n : ℤ), a ^ 2 ≤ 4 * p → 0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  intro a p m n h
  nlinarith [sq_nonneg (2 * m - a * n), mul_nonneg (sub_nonneg.mpr h) (sq_nonneg n)]

end MPP.Solutions.Bsd158
