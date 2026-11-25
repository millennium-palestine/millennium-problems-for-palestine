import Mathlib

namespace MPP.Solutions.Bsd221

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y), y ≠ W.toAffine.negY x y →
    ∃ (x' y' : K) (h' : W.toAffine.Nonsingular x' y'),
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
          WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some x' y' h' ∧
      x' * (2 * y + W.a₁ * x + W.a₃) ^ 2 = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  intro K _ _ W x y h hy
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hD' : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hD0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [← hD']
    exact sub_ne_zero.mpr hy
  refine ⟨_, _, WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.right),
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy, ?_⟩
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hD']
  have eND : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) *
      (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y :=
    div_mul_cancel₀ _ hD0
  have ha₁ : W.toAffine.a₁ = W.a₁ := rfl
  have ha₂ : W.toAffine.a₂ = W.a₂ := rfl
  have ha₄ : W.toAffine.a₄ = W.a₄ := rfl
  simp only [WeierstrassCurve.Affine.addX, ha₁, ha₂, ha₄, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
      (2 * y + W.a₁ * x + W.a₃) * (2 * y + W.a₁ * x + W.a₃) +
      (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * eND +
    (-(W.a₁ ^ 2) - 4 * W.a₂ - 8 * x) * hE

end MPP.Solutions.Bsd221
