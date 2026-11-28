import Mathlib

namespace MPP.Solutions.Bsd420

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (m : ℤ), ¬ (p : ℤ) ∣ m →
    ((Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // m • P = 0} : ℤ) ≤ m ^ 2) →
    (m ^ 2 ≤ (Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // m • P = 0} : ℤ)) →
    (Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // m • P = 0} : ℤ) = m ^ 2 := by
  intro p _ _ W _ m _ h1 h2
  exact le_antisymm h1 h2

end MPP.Solutions.Bsd420
