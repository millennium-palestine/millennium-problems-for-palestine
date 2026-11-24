import Mathlib
import MPP.Defs.BSD

namespace MPP.Solutions.Bsd003

open MPP.BSD WeierstrassCurve

theorem main : ∃ P : E32.toAffine.Point, P ≠ 0 ∧ 2 • P = 0 := by
  have hΔ : E32.toAffine.Δ ≠ 0 := by
    show E32.Δ ≠ 0
    simp [E32, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hEq : E32.toAffine.Equation 0 0 := by
    simp [WeierstrassCurve.Affine.equation_iff, E32]
  have hns : E32.toAffine.Nonsingular 0 0 :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq
  refine ⟨WeierstrassCurve.Affine.Point.some _ _ hns, WeierstrassCurve.Affine.Point.some_ne_zero hns,
    ?_⟩
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [WeierstrassCurve.Affine.negY, E32]

end MPP.Solutions.Bsd003
