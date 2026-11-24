import Mathlib
import MPP.Solutions.Bsd079
import MPP.Solutions.Bsd129

namespace MPP.Solutions.Bsd036

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ s : Finset E.toAffine.Point,
    ∀ P : E.toAffine.Point, ∃ Q ∈ s, ∃ R : E.toAffine.Point, P = Q + 2 • R := by
  intro E _
  exact MPP.Solutions.Bsd079.main E (fun E' _ p q h1 h2 h3 h4 h6 =>
    MPP.Solutions.Bsd129.main p q E' h1 h2 h3 h4 h6)

end MPP.Solutions.Bsd036
