import Mathlib
import MPP.Solutions.Bsd015

namespace MPP.Solutions.Bsd088

theorem main : ∀ (a : ℕ → ℂ) (s : ℂ), 3 / 2 < s.re →
    (∀ n : ℕ, 0 < n → ‖a n‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) →
    LSeriesSummable a s := by
  intro a s hs ha
  exact MPP.Solutions.Bsd015.main a s ha hs

end MPP.Solutions.Bsd088
