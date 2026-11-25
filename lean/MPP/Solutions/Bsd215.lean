import Mathlib

namespace MPP.Solutions.Bsd215

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (W : WeierstrassCurve K),
    W.a₁ ^ p = W.a₁ → W.a₂ ^ p = W.a₂ → W.a₃ ^ p = W.a₃ → W.a₄ ^ p = W.a₄ →
    ∀ (x₁ y₁ x₂ y₂ : K), x₁ ≠ x₂ →
      ∀ (h₁' : W.toAffine.Nonsingular (x₁ ^ p) (y₁ ^ p))
        (h₂' : W.toAffine.Nonsingular (x₂ ^ p) (y₂ ^ p))
        (h₃ : W.toAffine.Nonsingular
          ((WeierstrassCurve.Affine.addX W x₁ x₂ (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) ^ p)
          ((WeierstrassCurve.Affine.addY W x₁ x₂ y₁ (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) ^ p)),
        (WeierstrassCurve.Affine.Point.some (x₁ ^ p) (y₁ ^ p) h₁' +
          WeierstrassCurve.Affine.Point.some (x₂ ^ p) (y₂ ^ p) h₂' : W.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some
            ((WeierstrassCurve.Affine.addX W x₁ x₂ (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) ^ p)
            ((WeierstrassCurve.Affine.addY W x₁ x₂ y₁ (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) ^ p) h₃ := by
  intro p _ K _ _ _ W h1 h2 h3 h4 x₁ y₁ x₂ y₂ hx h₁' h₂' h₃
  have hX : ∀ a b l : K, WeierstrassCurve.Affine.addX W (a ^ p) (b ^ p) (l ^ p) =
      (WeierstrassCurve.Affine.addX W a b l) ^ p := by
    intro a b l
    unfold WeierstrassCurve.Affine.addX
    simp only [sub_pow_char, add_pow_char, mul_pow, ← pow_mul, h1, h2]
    ring
  have hY : ∀ a b c l : K, WeierstrassCurve.Affine.addY W (a ^ p) (b ^ p) (c ^ p) (l ^ p) =
      (WeierstrassCurve.Affine.addY W a b c l) ^ p := by
    intro a b c l
    have h1' : frobenius K p W.a₁ = W.a₁ := by rw [frobenius_def]; exact h1
    have h2' : frobenius K p W.a₂ = W.a₂ := by rw [frobenius_def]; exact h2
    have h3' : frobenius K p W.a₃ = W.a₃ := by rw [frobenius_def]; exact h3
    simp only [← frobenius_def]
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.negY
      WeierstrassCurve.Affine.addX
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, h1', h2', h3']
  have hx' : x₁ ^ p ≠ x₂ ^ p := fun h => hx ((frobenius K p).injective h)
  have hs : WeierstrassCurve.Affine.slope W (x₁ ^ p) (x₂ ^ p) (y₁ ^ p) (y₂ ^ p) =
      (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂) ^ p := by
    unfold WeierstrassCurve.Affine.slope
    rw [if_neg hx', if_neg hx, div_pow, sub_pow_char, sub_pow_char]
  have key : ∀ (x y x' y' : K) (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular x' y'),
      x = x' → y = y' →
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x' y' h' := by
    intro x y x' y' h h' hxe hye
    subst hxe
    subst hye
    rfl
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx']
  apply key
  · rw [hs]
    exact hX _ _ _
  · rw [hs]
    exact hY _ _ _ _

end MPP.Solutions.Bsd215
