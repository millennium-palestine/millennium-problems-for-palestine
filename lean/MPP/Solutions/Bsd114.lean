import Mathlib

namespace MPP.Solutions.Bsd114

theorem main : ∀ (p e u v x : ℚ), u ^ 2 - v ^ 2 * (e ^ 2 + p) = x → 2 * u * v - e * v ^ 2 = -1 →
    x ^ 2 + e * x + (e ^ 2 + p) = (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p)) ^ 2 := by
  intro p e u v x h1 h2
  linear_combination (e ^ 2 + p - 2 * (e ^ 2 + p) * u * v + e * u ^ 2) * h2 -
    (x + (u ^ 2 - v ^ 2 * (e ^ 2 + p)) + e) * h1

end MPP.Solutions.Bsd114
