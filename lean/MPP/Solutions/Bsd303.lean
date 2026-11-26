import Mathlib
import MPP.Solutions.Bsd265

namespace MPP.Solutions.Bsd303

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) *
      ((2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 -
        (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3) = 0 := by
  intro K _ _ W x y h hD h5
  -- 4P + P = 5P = 0, so 4P = -P
  have e : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
    rw [show (5 : ℤ) = 4 + 1 by norm_num, add_zsmul, one_zsmul]
  have h4 : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      -(WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
    apply eq_neg_of_add_eq_zero_left
    rw [e, h5]
  -- the negative of P is the affine point (x, negY x y)
  have hn : W.toAffine.Nonsingular x (W.toAffine.negY x y) :=
    (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
  have h4' : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x (W.toAffine.negY x y) hn := by
    rw [h4]
    exact WeierstrassCurve.Affine.Point.neg_some h
  -- the seven-torsion step (bsd-265) with x4 = x
  have key := MPP.Solutions.Bsd265.main K W x y x (W.toAffine.negY x y) h hn hD h4'
  linear_combination key

end MPP.Solutions.Bsd303
