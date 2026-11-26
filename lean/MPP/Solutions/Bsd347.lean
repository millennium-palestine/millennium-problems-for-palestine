import Mathlib

namespace MPP.Solutions.Bsd347

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂), x₁ ≠ x₂ →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      x₃ = ((y₁ - y₂) / (x₁ - x₂)) ^ 2 + W.a₁ * ((y₁ - y₂) / (x₁ - x₂)) - W.a₂ - x₁ - x₂ := by
  intro K _ _ W x₁ y₁ x₂ y₂ h₁ h₂ hx
  have hsum := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx
  refine ⟨_, _, _, hsum, ?_⟩
  unfold WeierstrassCurve.Affine.addX
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]

end MPP.Solutions.Bsd347
