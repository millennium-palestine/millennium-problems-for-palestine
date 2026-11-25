import Mathlib
import MPP.Solutions.Bsd199
import MPP.Solutions.Bsd207

namespace MPP.Solutions.Bsd209

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x₁ y₁ x₂ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂), x₁ ≠ x₂ →
    ∃ (x₃ y₃ x₄ y₄ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃) (h₄ : W.toAffine.Nonsingular x₄ y₄),
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ + -WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₄ y₄ h₄ ∧
      x₃ * x₄ * (x₁ - x₂) ^ 2 =
        x₁ ^ 2 * x₂ ^ 2 - W.a₁ * W.a₃ * x₁ * x₂ - 2 * W.a₄ * x₁ * x₂ - W.a₃ ^ 2 * (x₁ + x₂) -
          4 * W.a₆ * (x₁ + x₂) + W.a₄ ^ 2 + W.a₁ * W.a₃ * W.a₄ - W.a₁ ^ 2 * W.a₆ - W.a₂ * W.a₃ ^ 2 -
          4 * W.a₂ * W.a₆ := by
  intro K _ _ W x₁ y₁ x₂ y₂ h₁ h₂ hx
  obtain ⟨x₃, y₃, h₃, hadd, hx₃⟩ := MPP.Solutions.Bsd199.main K W x₁ y₁ x₂ y₂ h₁ h₂ hx
  have h₂' : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
    (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr h₂
  obtain ⟨x₄, y₄, h₄, hsub, hx₄⟩ :=
    MPP.Solutions.Bsd199.main K W x₁ y₁ x₂ (W.toAffine.negY x₂ y₂) h₁ h₂' hx
  refine ⟨x₃, y₃, x₄, y₄, h₃, h₄, hadd, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    exact hsub
  · have key := MPP.Solutions.Bsd207.main K W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ x₁ y₁ x₂ y₂
      ((WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.left)
      ((WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂.left) hx
    simp only [WeierstrassCurve.Affine.negY] at hx₄
    rw [hx₃, hx₄]
    linear_combination key

end MPP.Solutions.Bsd209
