import Mathlib

namespace MPP.Solutions.Bsd268

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y x' y' : K)
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y'),
    (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x' y' h' →
    (x - x') * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  intro K _ _ W x y x' y' h h' hsum
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  by_cases hy : y = WeierstrassCurve.Affine.negY W x y
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy] at hsum
    exact absurd hsum (by simp)
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy] at hsum
    injection hsum with hx _
    have hD : y - WeierstrassCurve.Affine.negY W x y ≠ 0 := sub_ne_zero.mpr hy
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy] at hx
    simp only [WeierstrassCurve.Affine.addX] at hx
    obtain ⟨s, hs_def⟩ : ∃ s, s = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
        (y - WeierstrassCurve.Affine.negY W x y) := ⟨_, rfl⟩
    rw [← hs_def] at hx
    have hs : s * (y - WeierstrassCurve.Affine.negY W x y) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [hs_def]
      exact div_mul_cancel₀ _ hD
    simp only [WeierstrassCurve.Affine.negY] at hs
    subst hx
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x - 4 * (3 * x + W.a₂ - s ^ 2 - W.a₁ * s)) * hE
      - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y + s * (2 * y + W.a₁ * x + W.a₃) +
          W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hs

end MPP.Solutions.Bsd268
