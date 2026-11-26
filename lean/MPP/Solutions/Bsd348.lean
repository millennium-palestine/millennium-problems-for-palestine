import Mathlib

namespace MPP.Solutions.Bsd348

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y), 2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      x₃ = ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) ^ 2 +
        W.a₁ * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) - W.a₂ - 2 * x := by
  intro K _ _ W x y h hne
  have hy : y ≠ W.toAffine.negY x y := by
    intro e
    apply hne
    unfold WeierstrassCurve.Affine.negY at e
    linear_combination e
  have hsum := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  refine ⟨_, _, _, hsum, ?_⟩
  have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    unfold WeierstrassCurve.Affine.negY
    ring
  unfold WeierstrassCurve.Affine.addX
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hd]
  ring

end MPP.Solutions.Bsd348
