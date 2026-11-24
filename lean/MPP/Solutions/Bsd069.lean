import Mathlib

namespace MPP.Solutions.Bsd069

theorem main : ∀ (E : WeierstrassCurve ℚ), ∃ (p q : ℚ) (C : WeierstrassCurve.VariableChange ℚ),
    (C • E).a₁ = 0 ∧ (C • E).a₂ = 0 ∧ (C • E).a₃ = 0 ∧ (C • E).a₄ = p ∧ (C • E).a₆ = q := by
  intro E
  obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
  exact ⟨(C • E).a₄, (C • E).a₆, C, hC.a₁, hC.a₂, hC.a₃, rfl, rfl⟩

end MPP.Solutions.Bsd069
