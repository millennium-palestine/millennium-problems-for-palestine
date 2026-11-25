import Mathlib

namespace MPP.Solutions.Bsd208

theorem main : ∀ (K : Type) [Field K] (a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ : K),
    y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ = x₁ ^ 3 + a₂ * x₁ ^ 2 + a₄ * x₁ + a₆ →
    y₂ ^ 2 + a₁ * x₂ * y₂ + a₃ * y₂ = x₂ ^ 3 + a₂ * x₂ ^ 2 + a₄ * x₂ + a₆ →
    x₁ ≠ x₂ →
    (((y₂ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((y₂ - y₁) / (x₂ - x₁)) - a₂ - x₁ - x₂) +
      (((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) ^ 2 + a₁ * ((-y₂ - a₁ * x₂ - a₃ - y₁) / (x₂ - x₁)) - a₂ - x₁ - x₂) =
    (a₁ ^ 2 * x₁ * x₂ + a₁ * a₃ * (x₁ + x₂) + 4 * a₂ * x₁ * x₂ + a₃ ^ 2 + 2 * a₄ * (x₁ + x₂) + 4 * a₆ +
      2 * x₁ * x₂ * (x₁ + x₂)) / (x₂ - x₁) ^ 2 := by
  intro K _ a₁ a₂ a₃ a₄ a₆ x₁ y₁ x₂ y₂ E₁ E₂ h
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have key : ((y₂ - y₁) ^ 2 + a₁ * (y₂ - y₁) * (x₂ - x₁) - (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) +
      ((-y₂ - a₁ * x₂ - a₃ - y₁) ^ 2 + a₁ * (-y₂ - a₁ * x₂ - a₃ - y₁) * (x₂ - x₁) -
        (a₂ + x₁ + x₂) * (x₂ - x₁) ^ 2) =
      a₁ ^ 2 * x₁ * x₂ + a₁ * a₃ * (x₁ + x₂) + 4 * a₂ * x₁ * x₂ + a₃ ^ 2 + 2 * a₄ * (x₁ + x₂) + 4 * a₆ +
        2 * x₁ * x₂ * (x₁ + x₂) := by
    linear_combination 2 * E₁ + 2 * E₂
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
  rw [e3, e4, ← add_div, key]

end MPP.Solutions.Bsd208
