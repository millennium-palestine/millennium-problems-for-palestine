import Mathlib

namespace MPP.Solutions.Bsd232

theorem main : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R),
    W.b₂ ^ 2 * (2 * W.b₄) ^ 2 - 4 * 4 * (2 * W.b₄) ^ 3 - 4 * W.b₂ ^ 3 * W.b₆ - 27 * 4 ^ 2 * W.b₆ ^ 2 +
      18 * 4 * W.b₂ * (2 * W.b₄) * W.b₆ = 16 * W.Δ := by
  intro R _ W
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

end MPP.Solutions.Bsd232
