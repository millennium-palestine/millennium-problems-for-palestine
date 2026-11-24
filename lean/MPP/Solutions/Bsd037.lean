import Mathlib

namespace MPP.Solutions.Bsd037

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (x y : ℚ) (h : E.toAffine.Nonsingular x y),
    y ≠ E.toAffine.negY x y →
    ∃ (x' y' : ℚ) (h' : E.toAffine.Nonsingular x' y'),
      WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some x' y' h' ∧
      x' * (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆) =
        x ^ 4 - E.b₄ * x ^ 2 - 2 * E.b₆ * x - E.b₈ := by
  intro E _ x y h hy
  have hcurve : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  have hs : y - E.toAffine.negY x y = 2 * y + E.a₁ * x + E.a₃ := by
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hne : 2 * y + E.a₁ * x + E.a₃ ≠ 0 := by
    rw [← hs]
    exact sub_ne_zero.mpr hy
  refine ⟨_, _, _, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy, ?_⟩
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hs]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.toAffine]
  have e : ∀ m s : ℚ, s ≠ 0 →
      (m / s) ^ 2 + E.a₁ * (m / s) - E.a₂ - x - x =
        (m ^ 2 + E.a₁ * m * s - (E.a₂ + 2 * x) * s ^ 2) / s ^ 2 := by
    intro m s hs0
    field_simp
    ring
  rw [e _ _ hne, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hne)]
  linear_combination (-(E.a₁ ^ 2 * x + E.a₁ * E.a₃ + 4 * E.a₂ * x + 2 * E.a₄ + 6 * x ^ 2) ^ 2) * hcurve

end MPP.Solutions.Bsd037
