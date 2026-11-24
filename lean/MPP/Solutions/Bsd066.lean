import Mathlib

namespace MPP.Solutions.Bsd066

theorem main : ∀ (K : Type) [Field K] (a b c s : K), a ≠ 0 → b ≠ 0 → a * b * c = s ^ 2 →
    ∃ r : K, c = a * b * r ^ 2 := by
  intro K _ a b c s ha hb h
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  refine ⟨s / (a * b), ?_⟩
  have h2 : a * b * (s / (a * b)) ^ 2 = s ^ 2 / (a * b) := by
    rw [div_pow]
    field_simp
  rw [h2, eq_div_iff hab]
  linear_combination h

end MPP.Solutions.Bsd066
