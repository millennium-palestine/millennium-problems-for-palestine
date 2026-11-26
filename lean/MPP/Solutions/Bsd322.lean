import Mathlib

namespace MPP.Solutions.Bsd322

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (X : ℤ → A),
    (∀ j : ℤ, -4 ≤ j → j ≤ 4 →
      X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0) →
    (∀ j : ℤ, -3 ≤ j → j ≤ 3 →
      X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0) →
    (∀ j : ℤ, -2 ≤ j → j ≤ 2 →
      X (j + 4) * X (j - 4) - (d * b) ^ 2 * X (j + 1) * X (j - 1)
        + (d * b ^ 4 - c ^ 3) * c * X j ^ 2 = 0) →
    X (-4) * X (-3) * (X 5 * X (-5) - (d * b ^ 4 - c ^ 3) ^ 2 * X 1 * X (-1)
      + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X 0 ^ 2) = 0 := by
  intro A _ b c d X h2 h3 h4
  have e2m4 := h2 (-4) (by norm_num) (by norm_num)
  have e2m3 := h2 (-3) (by norm_num) (by norm_num)
  have e2m2 := h2 (-2) (by norm_num) (by norm_num)
  have e2m1 := h2 (-1) (by norm_num) (by norm_num)
  have e20 := h2 (0) (by norm_num) (by norm_num)
  have e3m3 := h3 (-3) (by norm_num) (by norm_num)
  have e3m2 := h3 (-2) (by norm_num) (by norm_num)
  have e3m1 := h3 (-1) (by norm_num) (by norm_num)
  have e41 := h4 (1) (by norm_num) (by norm_num)
  norm_num at e2m4 e2m3 e2m2 e2m1 e20 e3m3 e3m2 e3m1 e41
  linear_combination (b ^ 2 * c ^ 2 * d ^ 1) * (X (0) * X (1)) * e2m4
    + (c ^ 4 * d ^ 1) * (X (-2) * X (1)) * e2m3
    + -(b ^ 4 * c ^ 1 * d ^ 2) * (X (-2) * X (1)) * e2m3
    + (c ^ 3 * d ^ 2) * (X (-1) * X (0)) * e2m3
    + -(b ^ 4 * d ^ 3) * (X (-1) * X (0)) * e2m3
    + -(b ^ 2 * c ^ 3 * d ^ 1) * (X (-4) * X (1)) * e2m2
    + -(b ^ 2 * c ^ 4 * d ^ 1) * (X (-3) * X (0)) * e2m2
    + -(b ^ 2 * c ^ 1 * d ^ 3) * (X (-3) * X (0)) * e2m2
    + (b ^ 2 * c ^ 3 * d ^ 2) * (X (-2) * X (-1)) * e2m2
    + -(b ^ 6 * d ^ 3) * (X (-2) * X (-1)) * e2m2
    + -(c ^ 2 * d ^ 2) * (X (-5) * X (0)) * e2m1
    + -(c ^ 5 * d ^ 1) * (X (-3) * X (-2)) * e2m1
    + (2) * (b ^ 4 * c ^ 2 * d ^ 2) * (X (-3) * X (-2)) * e2m1
    + (b ^ 6 * d ^ 2) * (X (-4) * X (-3)) * e20
    + -(b ^ 2 * c ^ 2 * d ^ 1) * (X (-2) * X (1)) * e3m3
    + (c ^ 4) * (X (-4) * X (1)) * e3m2
    + -(b ^ 4 * c ^ 1 * d ^ 1) * (X (-4) * X (1)) * e3m2
    + (b ^ 4 * c ^ 2 * d ^ 1) * (X (-3) * X (0)) * e3m2
    + (c ^ 2 * d ^ 2) * (X (-3) * X (0)) * e3m2
    + -(c ^ 4 * d ^ 1) * (X (-2) * X (-1)) * e3m2
    + (b ^ 4 * c ^ 1 * d ^ 2) * (X (-2) * X (-1)) * e3m2
    + (b ^ 2 * d ^ 2) * (X (-5) * X (0)) * e3m1
    + -(b ^ 6 * d ^ 2) * (X (-3) * X (-2)) * e3m1
    + (1) * (X (-5) * X (-4)) * e41

end MPP.Solutions.Bsd322
