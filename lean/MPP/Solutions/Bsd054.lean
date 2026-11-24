import Mathlib

namespace MPP.Solutions.Bsd054

theorem main : ∀ (p q : ℚ) (E : WeierstrassCurve ℚ), E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    ∀ (x1 y1 x2 y2 : ℚ) (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2),
      x1 ≠ x2 →
      ∃ (x3 y3 : ℚ) (h3 : E.toAffine.Nonsingular x3 y3),
        WeierstrassCurve.Affine.Point.some _ _ h1 + WeierstrassCurve.Affine.Point.some _ _ h2 =
          WeierstrassCurve.Affine.Point.some _ _ h3 ∧
        x3 = ((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2 := by
  intro p q E ha1 ha2 ha3 ha4 ha6 x1 y1 x2 y2 h1 h2 hne
  refine ⟨E.toAffine.addX x1 x2 (E.toAffine.slope x1 x2 y1 y2),
    E.toAffine.addY x1 x2 y1 (E.toAffine.slope x1 x2 y1 y2),
    WeierstrassCurve.Affine.nonsingular_add h1 h2 (fun hxy => hne hxy.left), ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hne]
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    simp [WeierstrassCurve.Affine.addX, ha1, ha2]

end MPP.Solutions.Bsd054
