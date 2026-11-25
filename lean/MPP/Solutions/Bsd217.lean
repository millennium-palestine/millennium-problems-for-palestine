import Mathlib

namespace MPP.Solutions.Bsd217

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (x y₁ y₂ : K)
    (h₁ : W.toAffine.Nonsingular x y₁) (h₂ : W.toAffine.Nonsingular x y₂),
    (WeierstrassCurve.Affine.Point.some x y₁ h₁ : W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x y₂ h₂ ∨
      (WeierstrassCurve.Affine.Point.some x y₁ h₁ : W.toAffine.Point) =
        -(WeierstrassCurve.Affine.Point.some x y₂ h₂ : W.toAffine.Point) := by
  intro K _ W x y₁ y₂ h₁ h₂
  have e₁ := (WeierstrassCurve.Affine.equation_iff (W := W) x y₁).mp h₁.1
  have e₂ := (WeierstrassCurve.Affine.equation_iff (W := W) x y₂).mp h₂.1
  have hfac : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x + W.a₃) = 0 := by
    linear_combination e₁ - e₂
  rcases mul_eq_zero.mp hfac with h | h
  · left
    have : y₁ = y₂ := sub_eq_zero.mp h
    subst this
    rfl
  · right
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨rfl, by rw [WeierstrassCurve.Affine.negY]; linear_combination h⟩

end MPP.Solutions.Bsd217
