import Mathlib
import MPP.Solutions.Bsd015

namespace MPP.Solutions.Bsd046

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (s : ℂ),
    (∀ n : ℕ, 0 < n → ‖((E.LFunction n : ℤ) : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) →
    3 / 2 < s.re → LSeriesSummable ((↑) ∘ E.LFunction) s := by
  intro E _ s hbound hs
  exact MPP.Solutions.Bsd015.main (fun n => ((E.LFunction n : ℤ) : ℂ)) s hbound hs

end MPP.Solutions.Bsd046
