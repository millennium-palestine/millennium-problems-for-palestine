import Mathlib
import MPP.Solutions.Bsd332

namespace MPP.Solutions.Bsd352

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ),
    Odd m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → (W.preΨ' m).eval x = 0) →
    Nat.card {P : W.toAffine.Point // m • P = 0} ≤ m ^ 2 :=
  MPP.Solutions.Bsd332.main

end MPP.Solutions.Bsd352
