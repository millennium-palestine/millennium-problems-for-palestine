import Mathlib
import MPP.Solutions.Bsd104
import MPP.Solutions.Bsd105

namespace MPP.Solutions.Bsd110

theorem main : (∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
      |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) →
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ), 0 < n →
      ‖((E.LFunction n : ℤ) : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
  intro H E _ n hn
  exact MPP.Solutions.Bsd104.main E (fun v a q hg hp => MPP.Solutions.Bsd105.main H E v a q hg hp) n hn

end MPP.Solutions.Bsd110
