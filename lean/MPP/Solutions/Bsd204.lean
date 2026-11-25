import Mathlib

namespace MPP.Solutions.Bsd204

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (k : ℕ)
    (x y : K) (h : W.toAffine.Nonsingular x y),
    (2 * k + 1) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
      (k + 1) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        -(k • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)) := by
  intro K _ _ W _ k x y h hm
  apply eq_neg_of_add_eq_zero_left
  rw [← add_nsmul, show k + 1 + k = 2 * k + 1 by ring, hm]

end MPP.Solutions.Bsd204
