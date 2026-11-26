import Mathlib

namespace MPP.Solutions.Bsd283

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  intro K _ W
  rw [show (5 : ℕ) = 2 * (0 + 2) + 1 from rfl, WeierstrassCurve.preΨ'_odd]
  simp [WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, pow_three]

end MPP.Solutions.Bsd283
