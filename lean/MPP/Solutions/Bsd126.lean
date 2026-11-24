import Mathlib
import MPP.Solutions.Bsd125

namespace MPP.Solutions.Bsd126

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    e1 ≠ e2 → e1 ≠ e3 → e2 ≠ e3 →
    ∃ (C : WeierstrassCurve.VariableChange ℚ) (f1 f2 f3 : ℤ), f1 + f2 + f3 = 0 ∧ f1 ≠ f2 ∧ f1 ≠ f3 ∧
      f2 ≠ f3 ∧ (C • E).a₁ = 0 ∧ (C • E).a₂ = 0 ∧ (C • E).a₃ = 0 ∧
      (C • E).a₄ = (f1 : ℚ) * (f2 : ℚ) + (f1 : ℚ) * (f3 : ℚ) + (f2 : ℚ) * (f3 : ℚ) ∧
      (C • E).a₆ = -((f1 : ℚ) * (f2 : ℚ) * (f3 : ℚ)) := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hs hp hq h12 h13 h23
  obtain ⟨d, hd0, f1, f2, f3, hf1, hf2, hf3⟩ := MPP.Solutions.Bsd125.main e1 e2 e3 hs h12 h13 h23
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  -- the change of variables x ↦ d²x, y ↦ d³y, that is u = 1/d and r = s = t = 0
  obtain ⟨C, hr, hs0, ht, hu⟩ : ∃ C : WeierstrassCurve.VariableChange ℚ, C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧
      ((C.u⁻¹ : ℚˣ) : ℚ) = (d : ℚ) :=
    ⟨⟨Units.mk0 (d : ℚ)⁻¹ (inv_ne_zero hdq), 0, 0, 0⟩, rfl, rfl, rfl, by simp⟩
  refine ⟨C, f1, f2, f3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : ((f1 + f2 + f3 : ℤ) : ℚ) = 0 := by
      push_cast
      rw [← hf1, ← hf2, ← hf3]
      linear_combination (d : ℚ) ^ 2 * hs
    exact_mod_cast h0
  · intro h
    have hh : (f1 : ℚ) = f2 := by exact_mod_cast h
    have h0 : (d : ℚ) ^ 2 * (e1 - e2) = 0 := by linear_combination hf1 - hf2 + hh
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hdq (pow_eq_zero_iff two_ne_zero |>.mp h')
    · exact h12 (sub_eq_zero.mp h')
  · intro h
    have hh : (f1 : ℚ) = f3 := by exact_mod_cast h
    have h0 : (d : ℚ) ^ 2 * (e1 - e3) = 0 := by linear_combination hf1 - hf3 + hh
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hdq (pow_eq_zero_iff two_ne_zero |>.mp h')
    · exact h13 (sub_eq_zero.mp h')
  · intro h
    have hh : (f2 : ℚ) = f3 := by exact_mod_cast h
    have h0 : (d : ℚ) ^ 2 * (e2 - e3) = 0 := by linear_combination hf2 - hf3 + hh
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hdq (pow_eq_zero_iff two_ne_zero |>.mp h')
    · exact h23 (sub_eq_zero.mp h')
  · rw [WeierstrassCurve.variableChange_a₁, ha1, hs0]
    ring
  · rw [WeierstrassCurve.variableChange_a₂, ha2, hs0, hr]
    ring
  · rw [WeierstrassCurve.variableChange_a₃, ha3, hr, ht]
    ring
  · rw [WeierstrassCurve.variableChange_a₄, ha4, hr, hs0, ht, hu, ← hf1, ← hf2, ← hf3]
    linear_combination (d : ℚ) ^ 4 * hp
  · rw [WeierstrassCurve.variableChange_a₆, ha6, hr, ht, hu, ← hf1, ← hf2, ← hf3]
    linear_combination (d : ℚ) ^ 6 * hq

end MPP.Solutions.Bsd126
