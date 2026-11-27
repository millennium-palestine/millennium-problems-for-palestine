import Mathlib

namespace MPP.Solutions.Bsd362

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂),
    W.a₁ = 0 → W.a₂ = 0 → W.a₃ = 0 → x₁ ≠ x₂ →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃) (x₄ y₄ : K) (h₄ : W.toAffine.Nonsingular x₄ y₄),
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + -WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₄ y₄ h₄ ∧
      (x₃ + x₄) * (x₁ - x₂) ^ 2 = 2 * (x₁ + x₂) * (x₁ * x₂ + W.a₄) + 4 * W.a₆ := by
  intro K _ _ W x₁ y₁ x₂ y₂ h₁ h₂ ha₁ ha₂ ha₃ hx
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hn := (WeierstrassCurve.Affine.nonsingular_neg x₂ y₂).mpr h₂
  have hsum := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  have hdiff := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := hn) hx
  have e₁ := h₁.1
  have e₂ := h₂.1
  rw [WeierstrassCurve.Affine.equation_iff] at e₁ e₂
  simp only [ha₁, ha₂, ha₃, zero_mul, add_zero] at e₁ e₂
  have hnadd := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ fun hxy => hx hxy.left
  have hndiff := WeierstrassCurve.Affine.nonsingular_add h₁ hn fun hxy => hx hxy.left
  refine ⟨_, _, hnadd, _, _, hndiff, hsum, hdiff, ?_⟩
  unfold WeierstrassCurve.Affine.addX
  simp only [WeierstrassCurve.Affine.slope_of_X_ne hx, WeierstrassCurve.Affine.negY, ha₁, ha₂, ha₃,
    zero_mul, sub_zero]
  have f₁ : y₁ ^ 2 = x₁ ^ 3 + W.a₄ * x₁ + W.a₆ := e₁
  have f₂ : y₂ ^ 2 = x₂ ^ 3 + W.a₄ * x₂ + W.a₆ := e₂
  have hA : (y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) = y₁ - y₂ := div_mul_cancel₀ _ hd
  have hB : (y₁ - -y₂) / (x₁ - x₂) * (x₁ - x₂) = y₁ - -y₂ := div_mul_cancel₀ _ hd
  linear_combination ((y₁ - y₂) / (x₁ - x₂) * (x₁ - x₂) + (y₁ - y₂)) * hA
    + ((y₁ - -y₂) / (x₁ - x₂) * (x₁ - x₂) + (y₁ - -y₂)) * hB + 2 * f₁ + 2 * f₂

end MPP.Solutions.Bsd362
