import Mathlib
import MPP.Solutions.Bsd283

namespace MPP.Solutions.Bsd364

open Polynomial

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    W.a₁ = 0 → W.a₂ = 0 → W.a₃ = 0 →
    W.preΨ' 5 =
      32 * (X ^ 6 + 5 * C W.a₄ * X ^ 4 + 20 * C W.a₆ * X ^ 3 - 5 * C (W.a₄ ^ 2) * X ^ 2
            - 4 * C (W.a₄ * W.a₆) * X - C (W.a₄ ^ 3) - 8 * C (W.a₆ ^ 2)) *
        (X ^ 3 + C W.a₄ * X + C W.a₆) ^ 2
      - (3 * X ^ 4 + 6 * C W.a₄ * X ^ 2 + 12 * C W.a₆ * X - C (W.a₄ ^ 2)) ^ 3 := by
  intro K _ W h1 h2 h3
  have hb2 : W.b₂ = 0 := by rw [WeierstrassCurve.b₂, h1, h2]; ring
  have hb4 : W.b₄ = 2 * W.a₄ := by rw [WeierstrassCurve.b₄, h1, h3]; ring
  have hb6 : W.b₆ = 4 * W.a₆ := by rw [WeierstrassCurve.b₆, h3]; ring
  have hb8 : W.b₈ = -(W.a₄ ^ 2) := by rw [WeierstrassCurve.b₈, h1, h2, h3]; ring
  rw [MPP.Solutions.Bsd283.main K W, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, hb2, hb4, hb6, hb8]
  simp only [map_pow, map_mul, map_neg, map_sub, map_zero, map_ofNat]
  ring

end MPP.Solutions.Bsd364
