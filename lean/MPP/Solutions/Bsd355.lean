import Mathlib
import MPP.Solutions.Bsd221

namespace MPP.Solutions.Bsd355

-- an affine point with 2 • P = 0 has 2y + a₁x + a₃ = 0
lemma two_key {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y)
    (hP : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0) :
    2 * y + W.a₁ * x + W.a₃ = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some] at hP
  have hy := (WeierstrassCurve.Affine.Point.some.inj hP).2
  simp only [WeierstrassCurve.Affine.negY] at hy
  linear_combination hy

-- the x-coordinate of an affine two-torsion point is a root of 4x³ + b₂x² + 2b₄x + b₆
lemma cubic_root {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y)
    (hP : 2 • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
  have hD := two_key W x y h hP
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp
    ((WeierstrassCurve.Affine.nonsingular_iff x y).mp h).1
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (2 * y + W.a₁ * x + W.a₃) * hD - 4 * heq

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 →
    (W.preΨ' 4).eval x = 0 := by
  intro K _ _ W x y h h4 h2
  -- 2P is not zero, so y is not the negative of itself: the doubling lemma applies
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply h2
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  -- the double 2P = (x2, y2) and x2 (2y + a₁x + a₃)² = x⁴ − b₄x² − 2b₆x − b₈
  obtain ⟨x2, y2, h2', hPP, hx2⟩ := MPP.Solutions.Bsd221.main K W x y h hyne
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hgD : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hE
  have hA : x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    linear_combination hx2 - x2 * hgD
  -- 2 • (2P) = 4 • P = 0, so the double is a two-torsion point
  have e : (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) +
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) := by
    abel
  have hQ : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x2 y2 h2' : W.toAffine.Point) = 0 := by
    rw [← hPP, two_nsmul, ← e, h4]
  have hf2 := cubic_root W x2 y2 h2' hQ
  have hH : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := W.b_relation
  -- resultant identity: (preΨ₄ x)² = f³ f(x2) - M (x2 f - g) + E (4 b₈ - b₂b₆ + b₄²)
  have key : (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2
      + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) ^ 2 = 0 := by
    linear_combination (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 * hf2
      - (4 * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2
          + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
            * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)
          + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2)
        + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
          * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈))
        + 2 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2) * hA
      + (W.b₂ ^ 2 * x ^ 6 + 6 * W.b₂ * W.b₄ * x ^ 5 + 7 * W.b₂ * W.b₆ * x ^ 4 + 4 * W.b₂ * W.b₈ * x ^ 3
        + 8 * W.b₂ * x ^ 7 + 8 * W.b₄ ^ 2 * x ^ 4 + 16 * W.b₄ * W.b₆ * x ^ 3 + 8 * W.b₄ * W.b₈ * x ^ 2
        + 28 * W.b₄ * x ^ 6 + 7 * W.b₆ ^ 2 * x ^ 2 + 6 * W.b₆ * W.b₈ * x + 38 * W.b₆ * x ^ 5
        + W.b₈ ^ 2 + 22 * W.b₈ * x ^ 4 + 13 * x ^ 8) * hH
  have h0 := (pow_eq_zero_iff two_ne_zero).mp key
  rw [W.preΨ'_four]
  simp [WeierstrassCurve.preΨ₄]
  linear_combination h0

end MPP.Solutions.Bsd355
