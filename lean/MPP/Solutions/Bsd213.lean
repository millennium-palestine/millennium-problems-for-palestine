import Mathlib

namespace MPP.Solutions.Bsd213

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (W : WeierstrassCurve K),
    W.a₁ ^ p = W.a₁ → W.a₂ ^ p = W.a₂ → W.a₃ ^ p = W.a₃ →
    ∀ x₁ x₂ y₁ ℓ : K,
      WeierstrassCurve.Affine.addY W (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (ℓ ^ p) =
        (WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ) ^ p := by
  intro p _ K _ _ W h1 h2 h3 x₁ x₂ y₁ ℓ
  have h1' : frobenius K p W.a₁ = W.a₁ := by rw [frobenius_def]; exact h1
  have h2' : frobenius K p W.a₂ = W.a₂ := by rw [frobenius_def]; exact h2
  have h3' : frobenius K p W.a₃ = W.a₃ := by rw [frobenius_def]; exact h3
  simp only [← frobenius_def]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.addX
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, h1', h2', h3']

end MPP.Solutions.Bsd213
