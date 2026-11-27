import Mathlib
import MPP.Solutions.Bsd316

namespace MPP.Solutions.Bsd332

-- the natural-number form of bsd-316 (accepted): the bound is an inequality in ℕ,
-- and the [W.IsElliptic] binder is not needed by the argument
theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ),
    Odd m → (m : K) ≠ 0 →
    (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → (W.preΨ' m).eval x = 0) →
    Nat.card {P : W.toAffine.Point // m • P = 0} ≤ m ^ 2 := by
  intro K _ _ W _ m hm hm0 H
  have h := MPP.Solutions.Bsd316.main K W m hm hm0 H
  exact_mod_cast h

end MPP.Solutions.Bsd332
