import Mathlib
import MPP.Defs.BSD
import MPP.Solutions.Bsd005

namespace MPP.Solutions.Bsd004

open MPP.BSD WeierstrassCurve

theorem main : Nat.card (AddCommGroup.torsion E32.toAffine.Point) = 4 := by
  haveI := MPP.Solutions.Bsd005.finite_points
  have htop : AddCommGroup.torsion E32.toAffine.Point = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [AddCommGroup.mem_torsion]
    exact isOfFinAddOrder_of_finite x
  have hbij : Function.Bijective
      (fun i : Fin 4 => (![0, WeierstrassCurve.Affine.Point.some 0 0 MPP.Solutions.Bsd005.ns00,
        WeierstrassCurve.Affine.Point.some 1 0 MPP.Solutions.Bsd005.ns10,
        WeierstrassCurve.Affine.Point.some (-1) 0 MPP.Solutions.Bsd005.nsm10] : Fin 4 → E32.toAffine.Point) i) := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact absurd hij (WeierstrassCurve.Affine.Point.some_ne_zero _)
        | exact absurd hij.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
        | (norm_num at hij)
    · intro P
      rcases MPP.Solutions.Bsd005.classify P with h | h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
      · exact ⟨3, by simp [h]⟩
  rw [htop, Nat.card_congr AddSubgroup.topEquiv.toEquiv]
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

end MPP.Solutions.Bsd004
