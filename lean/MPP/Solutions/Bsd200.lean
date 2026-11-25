import Mathlib

namespace MPP.Solutions.Bsd200

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y), 2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      x₃ = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) ^ 2 +
        W.a₁ * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) -
        W.a₂ - 2 * x := by
  intro K _ _ W x y h hd
  have hy : y ≠ W.toAffine.negY x y := by
    intro heq
    apply hd
    simp only [WeierstrassCurve.Affine.negY] at heq
    linear_combination heq
  have hden : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  refine ⟨W.toAffine.addX x x (W.toAffine.slope x x y y),
    W.toAffine.addY x x y (W.toAffine.slope x x y y),
    WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.right), ?_, ?_⟩
  · exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
  · simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_Y_ne (rfl : x = x) hy,
      hden]
    ring

end MPP.Solutions.Bsd200
