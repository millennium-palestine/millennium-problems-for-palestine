import Mathlib

namespace MPP.Solutions.Bsd270

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K)
    (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (h₃ : W.toAffine.Nonsingular x₃ y₃) (h₄ : W.toAffine.Nonsingular x₄ y₄)
    (h₂' : W.toAffine.Nonsingular x₂ (WeierstrassCurve.Affine.negY W x₂ y₂)),
    x₁ ≠ x₂ →
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ →
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
        WeierstrassCurve.Affine.Point.some x₂ (WeierstrassCurve.Affine.negY W x₂ y₂) h₂' :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₄ y₄ h₄ →
    (x₁ - x₂) ^ 2 * (x₃ + x₄) =
      2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆ := by
  intro K _ _ W x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ h₁ h₂ h₃ h₄ h₂' hx hsum₁ hsum₂
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hE₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ = x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.1
  have hE₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ = x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂.1
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx] at hsum₁
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx] at hsum₂
  injection hsum₁ with hx₃ _
  injection hsum₂ with hx₄ _
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx] at hx₃ hx₄
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY] at hx₃ hx₄
  obtain ⟨l, hl_def⟩ : ∃ l, l = (y₁ - y₂) / (x₁ - x₂) := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = (y₁ - (-y₂ - W.a₁ * x₂ - W.a₃)) / (x₁ - x₂) := ⟨_, rfl⟩
  rw [← hl_def] at hx₃
  rw [← hm_def] at hx₄
  have hl : l * (x₁ - x₂) = y₁ - y₂ := by
    rw [hl_def]
    exact div_mul_cancel₀ _ hd
  have hm : m * (x₁ - x₂) = y₁ - (-y₂ - W.a₁ * x₂ - W.a₃) := by
    rw [hm_def]
    exact div_mul_cancel₀ _ hd
  subst hx₃ hx₄
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (l * (x₁ - x₂) + (y₁ - y₂) + W.a₁ * (x₁ - x₂)) * hl +
    (m * (x₁ - x₂) + (y₁ - (-y₂ - W.a₁ * x₂ - W.a₃)) + W.a₁ * (x₁ - x₂)) * hm +
    2 * hE₁ + 2 * hE₂

end MPP.Solutions.Bsd270
