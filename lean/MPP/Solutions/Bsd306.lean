import Mathlib
import MPP.Solutions.Bsd246

namespace MPP.Solutions.Bsd306

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (x y : K)
    (h : W.toAffine.Nonsingular x y), (2 : K) ≠ 0 →
    (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (W.preΨ' 5).eval x = 0 := by
  intro K _ _ W _ x y h _ h5
  exact MPP.Solutions.Bsd246.main K W x y h h5

end MPP.Solutions.Bsd306
