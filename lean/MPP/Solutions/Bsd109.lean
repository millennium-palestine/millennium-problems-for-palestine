import Mathlib
import MPP.Solutions.Bsd046
import MPP.Solutions.Bsd104
import MPP.Solutions.Bsd105

namespace MPP.Solutions.Bsd109

theorem main : (∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
      |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) →
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (s : ℂ), 3 / 2 < s.re →
      LSeriesSummable ((↑) ∘ E.LFunction) s := by
  intro H E _ s hs
  exact MPP.Solutions.Bsd046.main E s
    (MPP.Solutions.Bsd104.main E (fun v a q hg hp => MPP.Solutions.Bsd105.main H E v a q hg hp)) hs

end MPP.Solutions.Bsd109
