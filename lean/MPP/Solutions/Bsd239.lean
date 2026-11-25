import Mathlib

namespace MPP.Solutions.Bsd239

theorem main : ∀ (K : Type) [Field K] (b2 b4 b6 x : K), (3 : K) ≠ 0 →
    12 * x ^ 4 + 4 * b2 * x ^ 3 + 12 * b4 * x ^ 2 + 12 * b6 * x + (b2 * b6 - b4 ^ 2) = 0 →
    48 * x ^ 3 + 12 * b2 * x ^ 2 + 24 * b4 * x + 12 * b6 = 0 →
    b2 ^ 3 * b6 - b2 ^ 2 * b4 ^ 2 - 36 * b2 * b4 * b6 + 32 * b4 ^ 3 + 108 * b6 ^ 2 = 0 := by
  intro K _ b2 b4 b6 x h3 hP hD
  have key : (3 : K) * (b2 ^ 3 * b6 - b2 ^ 2 * b4 ^ 2 - 36 * b2 * b4 * b6 + 32 * b4 ^ 3 + 108 * b6 ^ 2) = 0 := by
    linear_combination
      (-b2 ^ 2 * x - b2 * b4 + 9 * b2 * x ^ 2 + 42 * b4 * x + 27 * b6 + 36 * x ^ 3) * hD
        - 3 * (-b2 ^ 2 + 8 * b2 * x + 32 * b4 + 48 * x ^ 2) * hP
  exact (mul_eq_zero.mp key).resolve_left h3

end MPP.Solutions.Bsd239
