import Mathlib

namespace MPP.Solutions.Bsd031

-- the degree form at m = a, n = 2 is 4p − a², which is nonnegative
theorem main : ∀ (a p : ℤ), (∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + p * n ^ 2) → a ^ 2 ≤ 4 * p := by
  intro a p h
  have h2 := h a 2
  nlinarith [h2]

end MPP.Solutions.Bsd031
