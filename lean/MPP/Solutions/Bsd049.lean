import Mathlib

namespace MPP.Solutions.Bsd049

theorem main : ∀ (a1 a2 a3 a4 a6 x1 x2 y1 y2 u v : ℚ),
    y1 ^ 2 + a1 * x1 * y1 + a3 * y1 = x1 ^ 3 + a2 * x1 ^ 2 + a4 * x1 + a6 →
    y2 ^ 2 + a1 * x2 * y2 + a3 * y2 = x2 ^ 3 + a2 * x2 ^ 2 + a4 * x2 + a6 →
    x1 ≠ x2 →
    u = ((y1 - y2) / (x1 - x2)) ^ 2 + a1 * ((y1 - y2) / (x1 - x2)) - a2 - x1 - x2 →
    v = ((y1 + y2 + a1 * x2 + a3) / (x1 - x2)) ^ 2 + a1 * ((y1 + y2 + a1 * x2 + a3) / (x1 - x2))
      - a2 - x1 - x2 →
    (x1 - x2) ^ 2 * (u + v) = 2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2 + a1 ^ 2 * x1 * x2
        + a1 * a3 * (x1 + x2) + 4 * a2 * x1 * x2 + a3 ^ 2 + 2 * a4 * (x1 + x2) + 4 * a6 ∧
    (x1 - x2) ^ 2 * (u * v) = x1 ^ 2 * x2 ^ 2 - a1 * a3 * x1 * x2 - 2 * a4 * x1 * x2
        - a3 ^ 2 * (x1 + x2) - 4 * a6 * (x1 + x2) + a4 ^ 2 - a1 ^ 2 * a6 + a1 * a3 * a4
        - a2 * a3 ^ 2 - 4 * a2 * a6 := by
  intro a1 a2 a3 a4 a6 x1 x2 y1 y2 u v h1 h2 hne hu hv
  have hd : x1 - x2 ≠ 0 := sub_ne_zero.mpr hne
  have hD : (x1 - x2) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hU : (x1 - x2) ^ 2 * u = (y1 - y2) ^ 2 + a1 * (y1 - y2) * (x1 - x2)
      - (a2 + x1 + x2) * (x1 - x2) ^ 2 := by
    rw [hu]
    field_simp
    ring
  have hV : (x1 - x2) ^ 2 * v = (y1 + y2 + a1 * x2 + a3) ^ 2
      + a1 * (y1 + y2 + a1 * x2 + a3) * (x1 - x2) - (a2 + x1 + x2) * (x1 - x2) ^ 2 := by
    rw [hv]
    field_simp
    ring
  constructor
  · linear_combination hU + hV + 2 * h1 + 2 * h2
  · apply mul_left_cancel₀ hD
    linear_combination ((x1 - x2) ^ 2 * v) * hU
      + ((y1 - y2) ^ 2 + a1 * (y1 - y2) * (x1 - x2) - (a2 + x1 + x2) * (x1 - x2) ^ 2) * hV
      + (a1 ^ 2 * x1 * x2 - a1 ^ 2 * x2 ^ 2 + a1 * a3 * x1 - a1 * a3 * x2 + a1 * x1 * y1
        - 2 * a1 * x2 * y2 - a2 * x1 ^ 2 + 4 * a2 * x1 * x2 - 2 * a2 * x2 ^ 2 + a3 * y1
        - 2 * a3 * y2 + a4 * x1 + a6 - x1 ^ 3 + 2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2
        - 2 * x2 ^ 3 + y1 ^ 2 - 2 * y2 ^ 2) * h1
      + (-a1 ^ 2 * x1 ^ 2 + a1 ^ 2 * x1 * x2 - a1 * a3 * x1 + a1 * a3 * x2 + a1 * x2 * y2
        - 4 * a2 * x1 ^ 2 + 4 * a2 * x1 * x2 - a2 * x2 ^ 2 + a3 * y2 - 2 * a4 * x1 + a4 * x2
        - a6 - 4 * x1 ^ 3 + 2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2 - x2 ^ 3 + y2 ^ 2) * h2

end MPP.Solutions.Bsd049
