import Mathlib

namespace MPP.Solutions.Bsd207

theorem main : ∀ (K : Type) [Field K] (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ : K),
    y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆ →
    y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆ →
    x₁ ≠ x₂ →
    ((((y₂ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((y₂ - y₁) / (x₂ - x₁)) - a₂ - x₁ - x₂) *
      (((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) - a₂ - x₁ - x₂)) *
      (x₂ - x₁) ^ 2 =
    x₁ ^ 2 * x₂ ^ 2 - a₁ * a₃ * x₁ * x₂ - 2 * a₄ * x₁ * x₂ - a₃ ^ 2 * (x₁ + x₂) - 4 * a₆ * (x₁ + x₂) +
      a₄ ^ 2 + a₁ * a₃ * a₄ - a₁ ^ 2 * a₆ - a₂ * a₃ ^ 2 - 4 * a₂ * a₆ := by
  intro K _ a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ E₁ E₂ h
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hpoly : ((y₂ - y₁) ^ 2 + a₁ * (y₂ - y₁) * (x₂ - x₁) - (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) *
      ((-y₂ - a₁ * x₂ - a₃ - y₁) ^ 2 + a₁ * (-y₂ - a₁ * x₂ - a₃ - y₁) * (x₂ - x₁) -
        (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) =
      (x₁ ^ 2 * x₂ ^ 2 - a₁ * a₃ * x₁ * x₂ - 2 * a₄ * x₁ * x₂ - a₃ ^ 2 * (x₁ + x₂) - 4 * a₆ * (x₁ + x₂) +
        a₄ ^ 2 + a₁ * a₃ * a₄ - a₁ ^ 2 * a₆ - a₂ * a₃ ^ 2 - 4 * a₂ * a₆) * (x₂ - x₁) ^ 2 := by
    linear_combination
      (a₁ ^ 2 * x₁ * x₂ - a₁ ^ 2 * x₂ ^ 2 + a₁ * a₃ * x₁ - a₁ * a₃ * x₂ + a₁ * x₁ * y₁ - a₂ * x₁ ^ 2 +
        4 * a₂ * x₁ * x₂ - 4 * a₂ * x₂ ^ 2 + a₃ * y₁ + a₄ * x₁ - 2 * a₄ * x₂ - a₆ - x₁ ^ 3 +
        2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 4 * x₂ ^ 3 + y₁ ^ 2) * E₁ +
      (-a₁ ^ 2 * x₁ ^ 2 + a₁ ^ 2 * x₁ * x₂ - a₁ * a₃ * x₁ + a₁ * a₃ * x₂ - 2 * a₁ * x₁ * y₁ + a₁ * x₂ * y₂ -
        2 * a₂ * x₁ ^ 2 + 4 * a₂ * x₁ * x₂ - a₂ * x₂ ^ 2 - 2 * a₃ * y₁ + a₃ * y₂ + a₄ * x₂ + a₆ -
        2 * x₁ ^ 3 + 2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - x₂ ^ 3 - 2 * y₁ ^ 2 + y₂ ^ 2) * E₂
  have e3 : ((y₂ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((y₂ - y₁) / (x₂ - x₁)) - a₂ - x₁ - x₂ =
      ((y₂ - y₁) ^ 2 + a₁ * (y₂ - y₁) * (x₂ - x₁) - (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) / (x₂ - x₁) ^ 2 := by
    field_simp
    ring
  have e4 : ((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) -
      a₂ - x₁ - x₂ =
      ((-y₂ - a₁ * x₂ - a₃ - y₁) ^ 2 + a₁ * (-y₂ - a₁ * x₂ - a₃ - y₁) * (x₂ - x₁) -
        (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) / (x₂ - x₁) ^ 2 := by
    field_simp
    ring
  have hd2 : (x₂ - x₁) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  rw [e3, e4, div_mul_div_comm, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hd2 hd2)]
  linear_combination (x₂ - x₁) ^ 2 * hpoly

end MPP.Solutions.Bsd207
