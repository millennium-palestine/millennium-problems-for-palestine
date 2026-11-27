import Mathlib

namespace MPP.Solutions.Bsd375

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y), 2 * y + W.a₁ * x + W.a₃ = 0 →
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
  intro K _ _ W x y h hy
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination hy

end MPP.Solutions.Bsd375
