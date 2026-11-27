import Mathlib

namespace MPP.Solutions.Bsd400

theorem main : ∀ (p : ℕ) (a : ℤ), |(a : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) ↔ a ^ 2 ≤ 4 * (p : ℤ) := by
  intro p a
  have hs : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have habs : |(a : ℝ)| ^ 2 = (a : ℝ) ^ 2 := sq_abs _
  constructor
  · intro h
    have h1 : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
      nlinarith [abs_nonneg (a : ℝ)]
    exact_mod_cast h1
  · intro h
    have h1 : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by exact_mod_cast h
    nlinarith [abs_nonneg (a : ℝ)]

end MPP.Solutions.Bsd400
