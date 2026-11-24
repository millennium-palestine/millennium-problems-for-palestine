import Mathlib

namespace MPP.Solutions.Bsd119

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    ∀ (x y x3 y3 : ℚ) (h : E.toAffine.Nonsingular x y) (h1 : E.toAffine.Nonsingular e1 0)
      (h3 : E.toAffine.Nonsingular x3 y3),
      WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some e1 0 h1 =
        WeierstrassCurve.Affine.Point.some x3 y3 h3 → x ≠ e1 →
      (x3 - e1) * (x - e1) = (e1 - e2) * (e1 - e3) := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hsum hp hq x y x3 y3 h h1 h3 hadd hne
  have hcurve : y ^ 2 = (x - e1) * (x - e2) * (x - e3) := by
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + x ^ 2 * hsum + x * hp + hq
  have hxy : ¬(x = e1 ∧ y = E.toAffine.negY e1 0) := fun hc => hne hc.1
  rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.some.injEq] at hadd
  obtain ⟨hX, -⟩ := hadd
  have hslope : E.toAffine.slope x e1 y 0 = y / (x - e1) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    simp
  rw [hslope] at hX
  simp only [WeierstrassCurve.Affine.addX, ha1, ha2] at hX
  have key : (y / (x - e1)) ^ 2 * (x - e1) = (x - e2) * (x - e3) := by
    rw [div_pow, hcurve]
    field_simp
  rw [← hX]
  have he3 : e3 = -e1 - e2 := by linarith
  subst he3
  linear_combination key

end MPP.Solutions.Bsd119
