import Mathlib

namespace MPP.Solutions.Bsd212

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (W : WeierstrassCurve K),
    W.a₁ ^ p = W.a₁ → W.a₂ ^ p = W.a₂ →
    ∀ x₁ x₂ ℓ : K,
      WeierstrassCurve.Affine.addX W (x₁ ^ p) (x₂ ^ p) (ℓ ^ p) =
        (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ) ^ p := by
  intro p _ K _ _ W h1 h2 x₁ x₂ ℓ
  unfold WeierstrassCurve.Affine.addX
  simp only [sub_pow_char, add_pow_char, mul_pow, ← pow_mul, h1, h2]
  ring

end MPP.Solutions.Bsd212
