import Mathlib

namespace MPP.Solutions.Bsd241

theorem main : ∀ (K : Type) [Field K] (b2 b4 b6 x : K),
    12 * x ^ 4 + 4 * b2 * x ^ 3 + 12 * b4 * x ^ 2 + 12 * b6 * x + (b2 * b6 - b4 ^ 2) = 0 →
    4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 = 0 →
    b2 ^ 3 * b6 - b2 ^ 2 * b4 ^ 2 - 36 * b2 * b4 * b6 + 32 * b4 ^ 3 + 108 * b6 ^ 2 = 0 := by
  intro K _ b2 b4 b6 x hP hg
  linear_combination
    (4 * (-b2 ^ 2 * x - b2 * b4 + 9 * b2 * x ^ 2 + 42 * b4 * x + 27 * b6 + 36 * x ^ 3)) * hg
      - (-b2 ^ 2 + 8 * b2 * x + 32 * b4 + 48 * x ^ 2) * hP

end MPP.Solutions.Bsd241
