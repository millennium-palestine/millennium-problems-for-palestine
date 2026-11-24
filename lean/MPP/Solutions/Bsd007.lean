import Mathlib
import MPP.Defs.BSD

namespace MPP.Solutions.Bsd007

open MPP.BSD WeierstrassCurve

theorem main : ∀ (x y : ℚ) (h : E32.toAffine.Nonsingular x y), y ≠ 0 →
    ∃ (x' y' : ℚ) (h' : E32.toAffine.Nonsingular x' y'),
      WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h =
        WeierstrassCurve.Affine.Point.some x' y' h' ∧
      x' = (x ^ 2 + 1) ^ 2 / (4 * y ^ 2) := by
  intro x y h hy
  have hcurve : y ^ 2 = x ^ 3 - x := by
    have h1 := h.1
    simp [WeierstrassCurve.Affine.equation_iff, E32] at h1
    linarith
  have hyy : y ≠ E32.toAffine.negY x y := by
    intro hc
    apply hy
    simp [WeierstrassCurve.Affine.negY, E32] at hc
    linarith
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyy]
  refine ⟨_, _, _, rfl, ?_⟩
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyy]
  simp [WeierstrassCurve.Affine.addX, E32]
  have hy2 : (y ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 hy
  field_simp
  linear_combination (-32 * x) * hcurve

end MPP.Solutions.Bsd007
