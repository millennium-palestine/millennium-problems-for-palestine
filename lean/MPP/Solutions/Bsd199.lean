import Mathlib

namespace MPP.Solutions.Bsd199

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂), x₁ ≠ x₂ →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      x₃ = ((y₂ - y₁) / (x₂ - x₁)) ^ 2 + W.a₁ * ((y₂ - y₁) / (x₂ - x₁)) - W.a₂ - x₁ - x₂ := by
  intro K _ _ W x₁ y₁ x₂ y₂ h₁ h₂ hx
  have hs : (y₁ - y₂) / (x₁ - x₂) = (y₂ - y₁) / (x₂ - x₁) := by
    rw [← neg_sub y₁ y₂, ← neg_sub x₁ x₂, neg_div_neg_eq]
  refine ⟨W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂),
    W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂),
    WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun hxy => hx hxy.left), ?_, ?_⟩
  · exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
  · simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_X_ne hx, hs]

end MPP.Solutions.Bsd199
