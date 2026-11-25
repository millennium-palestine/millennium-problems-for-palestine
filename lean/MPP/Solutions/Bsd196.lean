import Mathlib

namespace MPP.Solutions.Bsd196

theorem main : ∀ (K : Type) [Field K] (a₁ a₂ a₃ a₄ a₆ x y₁ y₂ : K),
    y₁ ^ 2 + a₁ * x * y₁ + a₃ * y₁ = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ →
    y₂ ^ 2 + a₁ * x * y₂ + a₃ * y₂ = x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆ →
    y₂ = y₁ ∨ y₂ = -y₁ - a₁ * x - a₃ := by
  intro K _ a₁ a₂ a₃ a₄ a₆ x y₁ y₂ h₁ h₂
  have h : (y₂ - y₁) * (y₂ + y₁ + a₁ * x + a₃) = 0 := by
    linear_combination h₂ - h₁
  rcases mul_eq_zero.mp h with h' | h'
  · left
    linear_combination h'
  · right
    linear_combination h'

end MPP.Solutions.Bsd196
