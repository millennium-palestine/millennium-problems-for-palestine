import Mathlib

namespace MPP.Solutions.Bsd201

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    3 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
  intro K _ _ W x y h h3 hD0
  have hy : y = W.toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination hD0
  have hP2 := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁ := h) hy
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul, hP2, zero_add] at h3
  exact WeierstrassCurve.Affine.Point.some_ne_zero h h3

end MPP.Solutions.Bsd201
