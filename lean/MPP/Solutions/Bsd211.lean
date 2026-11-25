import Mathlib

namespace MPP.Solutions.Bsd211

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (W : WeierstrassCurve K),
    W.a₁ ^ p = W.a₁ → W.a₂ ^ p = W.a₂ → W.a₄ ^ p = W.a₄ → W.a₃ ^ p = W.a₃ →
    ∀ x₁ x₂ y₁ y₂ : K,
      WeierstrassCurve.Affine.slope W (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂) ^ p := by
  intro p _ K _ _ _ W h1 h2 h4 h3 x₁ x₂ y₁ y₂
  have e : ∀ a : K, a ^ p = frobenius K p a := fun a => by rw [frobenius_def]
  have hinj : Function.Injective (frobenius K p) := (frobenius K p).injective
  have hc1 : frobenius K p W.a₁ = W.a₁ := by rw [← e]; exact h1
  have hc2 : frobenius K p W.a₂ = W.a₂ := by rw [← e]; exact h2
  have hc3 : frobenius K p W.a₃ = W.a₃ := by rw [← e]; exact h3
  have hc4 : frobenius K p W.a₄ = W.a₄ := by rw [← e]; exact h4
  have f2 : frobenius K p 2 = 2 := map_ofNat _ 2
  have f3 : frobenius K p 3 = 3 := map_ofNat _ 3
  have hN : ∀ a b : K, WeierstrassCurve.Affine.negY W (frobenius K p a) (frobenius K p b) =
      frobenius K p (WeierstrassCurve.Affine.negY W a b) := by
    intro a b
    unfold WeierstrassCurve.Affine.negY
    simp only [map_sub, map_neg, map_mul, hc1, hc3]
  unfold WeierstrassCurve.Affine.slope
  simp only [e]
  by_cases hx : x₁ = x₂
  · have hx' : frobenius K p x₁ = frobenius K p x₂ := by rw [hx]
    rw [if_pos hx', if_pos hx]
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
    · have hy' : frobenius K p y₁ = WeierstrassCurve.Affine.negY W (frobenius K p x₂) (frobenius K p y₂) := by
        rw [hN, hy]
      rw [if_pos hy', if_pos hy, map_zero]
    · have hy' : ¬ frobenius K p y₁ = WeierstrassCurve.Affine.negY W (frobenius K p x₂) (frobenius K p y₂) := by
        rw [hN]
        intro h
        exact hy (hinj h)
      rw [if_neg hy', if_neg hy]
      simp only [map_div₀, map_add, map_sub, map_mul, map_pow, f2, f3, hc1, hc2, hc4, hN]
  · have hx' : ¬ frobenius K p x₁ = frobenius K p x₂ := fun h => hx (hinj h)
    rw [if_neg hx', if_neg hx, map_div₀, map_sub, map_sub]

end MPP.Solutions.Bsd211
