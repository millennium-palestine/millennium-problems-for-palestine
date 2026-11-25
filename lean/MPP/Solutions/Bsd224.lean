import Mathlib

namespace MPP.Solutions.Bsd224

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 2) * normEDS b c d (m - 2) - b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        + c * normEDS b c d m ^ 2 = 0 →
    normEDS b c d (m + 3) * normEDS b c d (m - 1) - b ^ 2 * normEDS b c d (m + 2) * normEDS b c d m
        + c * normEDS b c d (m + 1) ^ 2 = 0 →
    normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1) *
        (normEDS b c d 4 * (normEDS b c d (m + 1) * normEDS b c d (m + 2) * normEDS b c d m)
          + b ^ 3 * (normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d (m + 3))
          - b * c * (normEDS b c d m ^ 2 * normEDS b c d (m + 3)
            + normEDS b c d (m - 1) * normEDS b c d (m + 2) ^ 2)) =
      normEDS b c d (m + 1) * normEDS b c d (m + 2) * normEDS b c d m *
        (normEDS b c d 4 * (normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1))
          + b ^ 3 * (normEDS b c d m * normEDS b c d (m - 2) * normEDS b c d (m + 2))
          - b * c * (normEDS b c d (m - 1) ^ 2 * normEDS b c d (m + 2)
            + normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2)) := by
  intro A _ b c d m h1 h2
  linear_combination (b * normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m + 2)
      * normEDS b c d (m - 2)) * h2
    - (b * normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m + 3) * normEDS b c d (m - 1)) * h1

end MPP.Solutions.Bsd224
