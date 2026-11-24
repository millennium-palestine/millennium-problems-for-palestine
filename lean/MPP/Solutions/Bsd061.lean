import Mathlib

namespace MPP.Solutions.Bsd061

theorem main : ∀ (a b c s : ℚ), a ≠ 0 → b ≠ 0 → a * b * c = s ^ 2 → ∃ r : ℚ, c = a * b * r ^ 2 := by
  intro a b c s ha hb h
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  refine ⟨s / (a * b), ?_⟩
  have h2 : a * b * (s / (a * b)) ^ 2 = s ^ 2 / (a * b) := by
    rw [div_pow]
    field_simp
  rw [h2, eq_div_iff hab]
  linear_combination h

end MPP.Solutions.Bsd061
