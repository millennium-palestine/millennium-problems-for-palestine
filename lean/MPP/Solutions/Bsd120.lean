import Mathlib

namespace MPP.Solutions.Bsd120

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    ∀ (x y x3 y3 : ℚ) (h : E.toAffine.Nonsingular x y) (h3 : E.toAffine.Nonsingular x3 y3),
      WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some x3 y3 h3 → y ≠ 0 →
      x3 - e1 = (((x - e1) ^ 2 - (e1 - e2) * (e1 - e3)) / (2 * y)) ^ 2 := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hs hp hq x y x3 y3 h h3 hadd hy
  have hcurve : y ^ 2 = (x - e1) * (x - e2) * (x - e3) := by
    have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    rw [ha1, ha2, ha3, ha4, ha6] at heq
    linear_combination heq + x ^ 2 * hs + x * hp + hq
  have hyy : y ≠ E.toAffine.negY x y := by
    intro hc
    apply hy
    have hneg : E.toAffine.negY x y = -y := by
      simp [WeierstrassCurve.Affine.negY, ha1, ha3]
    rw [hneg] at hc
    linarith
  have hxy : ¬(x = x ∧ y = E.toAffine.negY x y) := fun hc => hyy hc.2
  rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.some.injEq] at hadd
  obtain ⟨hX, -⟩ := hadd
  have hslope : E.toAffine.slope x x y y = (3 * x ^ 2 + p) / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyy]
    have hneg : E.toAffine.negY x y = -y := by
      simp [WeierstrassCurve.Affine.negY, ha1, ha3]
    rw [hneg]
    simp [ha1, ha2, ha4]
    ring_nf
  rw [hslope] at hX
  simp only [WeierstrassCurve.Affine.addX, ha1, ha2] at hX
  rw [← hX]
  have he3 : e3 = -e1 - e2 := by linarith
  subst he3
  subst hp
  have hkey : (3 * x ^ 2 + (e1 * e2 + e1 * (-e1 - e2) + e2 * (-e1 - e2))) ^ 2 =
      (2 * x + e1) * (4 * y ^ 2) + ((x - e1) ^ 2 - (e1 - e2) * (e1 - (-e1 - e2))) ^ 2 := by
    linear_combination (-4 * (2 * x + e1)) * hcurve
  have hy2 : (2 * y) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero two_ne_zero hy)
  field_simp
  linear_combination hkey

end MPP.Solutions.Bsd120
