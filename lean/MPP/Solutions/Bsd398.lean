import Mathlib

namespace MPP.Solutions.Bsd398

theorem main : ∀ (a p m n : ℤ),
    4 * (m ^ 2 - a * m * n + p * n ^ 2) = (2 * m - a * n) ^ 2 + (4 * p - a ^ 2) * n ^ 2 := by
  intro a p m n
  ring

end MPP.Solutions.Bsd398
