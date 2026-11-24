import Mathlib

namespace MPP.Solutions.Bsd071

theorem main : ∀ (E : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ),
    E.toAffine.Nonsingular x y →
      (C • E).toAffine.Nonsingular ((x - C.r) / (C.u : ℚ) ^ 2) ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) := by
  intro E C x y h
  have hu : (C.u : ℚ) ≠ 0 := C.u.ne_zero
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at h ⊢
  obtain ⟨hE, hne⟩ := h
  have hne' : (E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄) ≠ 0) ∨ (2 * y + E.a₁ * x + E.a₃ ≠ 0) := hne
  refine ⟨?_, ?_⟩
  · have h' : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
      (WeierstrassCurve.Affine.equation_iff x y).mp hE
    rw [WeierstrassCurve.Affine.equation_iff]
    change _ ^ 2 + (C • E).a₁ * _ * _ + (C • E).a₃ * _ =
      _ ^ 3 + (C • E).a₂ * _ ^ 2 + (C • E).a₄ * _ + (C • E).a₆
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination h'
  · by_contra hc
    simp only [not_or, not_not] at hc
    obtain ⟨g1, g2⟩ := hc
    have g1' : (C • E).a₁ * ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) -
        (3 * ((x - C.r) / (C.u : ℚ) ^ 2) ^ 2 + 2 * (C • E).a₂ * ((x - C.r) / (C.u : ℚ) ^ 2) + (C • E).a₄) = 0 := g1
    have g2' : 2 * ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) +
        (C • E).a₁ * ((x - C.r) / (C.u : ℚ) ^ 2) + (C • E).a₃ = 0 := g2
    have hid2 : 2 * ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) +
        (C • E).a₁ * ((x - C.r) / (C.u : ℚ) ^ 2) + (C • E).a₃ =
        ((C.u : ℚ) ^ 3)⁻¹ * (E.a₁ * x + E.a₃ + 2 * y) := by
      simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃,
        Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hid1 : (C • E).a₁ * ((y - C.s * (x - C.r) - C.t) / (C.u : ℚ) ^ 3) -
        (3 * ((x - C.r) / (C.u : ℚ) ^ 2) ^ 2 + 2 * (C • E).a₂ * ((x - C.r) / (C.u : ℚ) ^ 2) + (C • E).a₄) =
        ((C.u : ℚ) ^ 4)⁻¹ * ((E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄)) +
          C.s * (E.a₁ * x + E.a₃ + 2 * y)) := by
      simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
        WeierstrassCurve.variableChange_a₄, Units.val_inv_eq_inv_val]
      field_simp
      ring
    have eG2 : E.a₁ * x + E.a₃ + 2 * y = 0 := by
      rw [hid2] at g2'
      rcases mul_eq_zero.mp g2' with h0 | h0
      · exact absurd h0 (inv_ne_zero (pow_ne_zero 3 hu))
      · exact h0
    have hsum : (E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄)) + C.s * (E.a₁ * x + E.a₃ + 2 * y) = 0 := by
      rw [hid1] at g1'
      rcases mul_eq_zero.mp g1' with h0 | h0
      · exact absurd h0 (inv_ne_zero (pow_ne_zero 4 hu))
      · exact h0
    have eG1 : E.a₁ * y - (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄) = 0 := by
      linear_combination hsum - C.s * eG2
    rcases hne' with h1 | h2
    · exact h1 eG1
    · exact h2 (by linear_combination eG2)

end MPP.Solutions.Bsd071
