import Mathlib

namespace MPP.Solutions.Bsd170

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a : ℤ),
    (∀ m n : ℤ, ¬ (p : ℤ) ∣ m → 0 ≤ m ^ 2 - a * m * n + (p : ℤ) * n ^ 2) →
      ∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + (p : ℤ) * n ^ 2 := by
  intro p hp a H m n
  by_contra hneg
  push_neg at hneg
  have hD : 0 < (a ^ 2 - 4 * (p : ℤ)) * n ^ 2 := by
    nlinarith [sq_nonneg (2 * m - a * n)]
  have hn2 : 0 < n ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp at hD
    · positivity
  have hDpos : 0 < a ^ 2 - 4 * (p : ℤ) := by
    by_contra h
    push_neg at h
    nlinarith
  have hD1 : 1 ≤ a ^ 2 - 4 * (p : ℤ) := by linarith
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  by_cases hdvd : (p : ℤ) ∣ 2 * a
  · have hnd : ¬ (p : ℤ) ∣ 2 * a + 1 := by
      intro h
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub h hdvd
        simpa using this
      have := Int.eq_one_of_dvd_one (by linarith) h1
      linarith
    have := H (2 * a + 1) 4 hnd
    nlinarith
  · have := H (2 * a) 4 hdvd
    nlinarith

end MPP.Solutions.Bsd170
