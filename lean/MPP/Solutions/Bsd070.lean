import Mathlib

namespace MPP.Solutions.Bsd070

theorem main : ∀ (E : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ),
    E.toAffine.Equation x y →
      (C • E).toAffine.Equation ((x - C.r) / (C.u : ℚ) ^ 2) ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) := by
  intro E C x y h
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  have h' : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h
  rw [WeierstrassCurve.Affine.equation_iff]
  change _ ^ 2 + (C • E).a₁ * _ * _ + (C • E).a₃ * _ =
    _ ^ 3 + (C • E).a₂ * _ ^ 2 + (C • E).a₄ * _ + (C • E).a₆
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp
  linear_combination h'

end MPP.Solutions.Bsd070
