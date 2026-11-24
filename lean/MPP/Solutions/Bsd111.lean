import Mathlib
import MPP.Solutions.Bsd038
import MPP.Solutions.Bsd039

namespace MPP.Solutions.Bsd111

theorem main : (∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ s : Finset E.toAffine.Point,
      ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R) →
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], AddGroup.FG E.toAffine.Point := by
  intro hA E _
  obtain ⟨h, h0, hneg, hfin, ⟨C, hC⟩, ⟨D, hD⟩⟩ := MPP.Solutions.Bsd038.main E
  exact MPP.Solutions.Bsd039.main E.toAffine.Point h C D h0 hneg hC hD hfin (hA E)

end MPP.Solutions.Bsd111
