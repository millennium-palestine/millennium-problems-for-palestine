import Mathlib

namespace MPP.Solutions.Bsd125

theorem main : ∀ (e1 e2 e3 : ℚ), e1 + e2 + e3 = 0 → e1 ≠ e2 → e1 ≠ e3 → e2 ≠ e3 →
    ∃ d : ℤ, d ≠ 0 ∧ ∃ f1 f2 f3 : ℤ, (d : ℚ) ^ 2 * e1 = (f1 : ℚ) ∧ (d : ℚ) ^ 2 * e2 = (f2 : ℚ) ∧
      (d : ℚ) ^ 2 * e3 = (f3 : ℚ) := by
  intro e1 e2 e3 _ _ _ _
  have h1 : e1 * (e1.den : ℚ) = (e1.num : ℚ) := Rat.mul_den_eq_num e1
  have h2 : e2 * (e2.den : ℚ) = (e2.num : ℚ) := Rat.mul_den_eq_num e2
  have h3 : e3 * (e3.den : ℚ) = (e3.num : ℚ) := Rat.mul_den_eq_num e3
  have hm1 : (e1.den : ℤ) ≠ 0 := by exact_mod_cast e1.den_nz
  have hm2 : (e2.den : ℤ) ≠ 0 := by exact_mod_cast e2.den_nz
  have hm3 : (e3.den : ℤ) ≠ 0 := by exact_mod_cast e3.den_nz
  refine ⟨(e1.den : ℤ) * (e2.den : ℤ) * (e3.den : ℤ), mul_ne_zero (mul_ne_zero hm1 hm2) hm3,
    (e1.den : ℤ) * (e2.den : ℤ) * (e3.den : ℤ) * ((e2.den : ℤ) * (e3.den : ℤ)) * e1.num,
    (e1.den : ℤ) * (e2.den : ℤ) * (e3.den : ℤ) * ((e1.den : ℤ) * (e3.den : ℤ)) * e2.num,
    (e1.den : ℤ) * (e2.den : ℤ) * (e3.den : ℤ) * ((e1.den : ℤ) * (e2.den : ℤ)) * e3.num, ?_, ?_, ?_⟩
  · push_cast
    linear_combination ((e1.den : ℚ) * (e2.den : ℚ) * (e3.den : ℚ) * ((e2.den : ℚ) * (e3.den : ℚ))) * h1
  · push_cast
    linear_combination ((e1.den : ℚ) * (e2.den : ℚ) * (e3.den : ℚ) * ((e1.den : ℚ) * (e3.den : ℚ))) * h2
  · push_cast
    linear_combination ((e1.den : ℚ) * (e2.den : ℚ) * (e3.den : ℚ) * ((e1.den : ℚ) * (e2.den : ℚ))) * h3

end MPP.Solutions.Bsd125
