import Mathlib

namespace MPP.Solutions.Bsd205

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y), 2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    ∃ (x₃ y₃ : K) (h₃ : W.toAffine.Nonsingular x₃ y₃),
      (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h :
        W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ ∧
      x₃ * (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        x * (2 * y + W.a₁ * x + W.a₃) ^ 2 -
          (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) := by
  intro K _ _ W x y h hD
  have hy' : ¬ (y = -y - W.a₁ * x - W.a₃) := fun h' => hD (by linear_combination h')
  have hy : y ≠ W.toAffine.negY x y := fun h' => hy' (by simpa [WeierstrassCurve.Affine.negY] using h')
  have hc := (WeierstrassCurve.Affine.equation_iff' x y).mp h.1
  refine ⟨W.toAffine.addX x x (W.toAffine.slope x x y y), W.toAffine.addY x x y (W.toAffine.slope x x y y),
    WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.2),
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy, ?_⟩
  rw [WeierstrassCurve.Affine.slope_of_Y_ne' hy']
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hD' : y - (-y - W.a₁ * x - W.a₃) ≠ 0 := fun h0 => hD (by linear_combination h0)
  have hℓ := div_mul_cancel₀ (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) hD'
  generalize (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - (-y - W.a₁ * x - W.a₃)) = ℓ at hℓ ⊢
  linear_combination (ℓ * (y - (-y - W.a₁ * x - W.a₃)) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    + W.a₁ * (y - (-y - W.a₁ * x - W.a₃))) * hℓ + (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x)) * hc

end MPP.Solutions.Bsd205
