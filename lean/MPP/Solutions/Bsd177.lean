import Mathlib

namespace MPP.Solutions.Bsd177

theorem main : ∃ C : ℝ, ∀ p : ℕ, 3 ≤ p → ∀ m : ℕ, m ≤ p →
    (p : ℝ) / 2 + C * Real.sqrt (p : ℝ) < m →
    ∃ ℓ J K : ℕ, 1 ≤ ℓ ∧ 1 ≤ J ∧ ℓ * m < 2 * J * K ∧
      p * J + K + 3 * ((p - 1) / 2) + 3 * ℓ < ℓ * m := by
  refine ⟨4, ?_⟩
  intro p hp m _ h
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p := Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs17 : (1.7 : ℝ) ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hreal : (5 * p + 65 : ℝ) < 11 * m := by linarith
  have hnat : 5 * p + 65 < 11 * m := by exact_mod_cast hreal
  refine ⟨11, 1, 11 * m / 2 + 1, by norm_num, le_refl _, ?_, ?_⟩
  · omega
  · omega

end MPP.Solutions.Bsd177
