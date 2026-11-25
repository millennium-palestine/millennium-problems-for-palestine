import Mathlib

namespace MPP.Solutions.Bsd202

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    3 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
      ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) ^ 2 +
        W.a₁ * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) -
        W.a₂ - 2 * x = x := by
  intro K _ _ W x y h h3 hD
  -- the doubling formula of bsd-200, inlined
  have hy : y ≠ W.toAffine.negY x y := by
    intro heq
    apply hD
    simp only [WeierstrassCurve.Affine.negY] at heq
    linear_combination heq
  have hden : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hdbl := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  -- 3 • P = 0 gives 2 • P = −P
  rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, two_nsmul, one_nsmul] at h3
  have h2 := eq_neg_of_add_eq_zero_left h3
  rw [hdbl, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h2
  have h5 := h2.1
  rw [WeierstrassCurve.Affine.slope_of_Y_ne (rfl : x = x) hy, hden] at h5
  simp only [WeierstrassCurve.Affine.addX] at h5
  linear_combination h5

end MPP.Solutions.Bsd202
