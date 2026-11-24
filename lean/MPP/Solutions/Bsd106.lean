import Mathlib

namespace MPP.Solutions.Bsd106

theorem main : ∀ p q : ℚ, ∃ u : ℚ, u ≠ 0 ∧ ∃ a b : ℤ, u ^ 4 * p = a ∧ u ^ 6 * q = b := by
  intro p q
  have hp : (p.den : ℚ) ≠ 0 := by exact_mod_cast p.den_nz
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hpn : p * (p.den : ℚ) = (p.num : ℚ) := Rat.mul_den_eq_num p
  have hqn : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  refine ⟨(p.den : ℚ) * (q.den : ℚ), mul_ne_zero hp hq,
    (p.den : ℤ) ^ 3 * (q.den : ℤ) ^ 4 * p.num, (p.den : ℤ) ^ 6 * (q.den : ℤ) ^ 5 * q.num, ?_, ?_⟩
  · push_cast
    rw [← hpn]
    ring
  · push_cast
    rw [← hqn]
    ring

end MPP.Solutions.Bsd106
