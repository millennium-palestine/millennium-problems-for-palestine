import Mathlib

namespace MPP.Solutions.Bsd133

-- the discriminant step of bsd-132, stated for an arbitrary trace a
theorem form_nonneg_of_disc (a p m n : ℤ) (h : a ^ 2 ≤ 4 * p) :
    0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  nlinarith [sq_nonneg (2 * m - a * n), mul_nonneg (sub_nonneg.2 h) (sq_nonneg n)]

-- apply the step with a = p + 1 − #E(F_p) and the Hasse hypothesis as h
theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (m n : ℤ),
    ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤ 4 * (p : ℤ) →
      0 ≤ m ^ 2 - ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) * m * n + (p : ℤ) * n ^ 2 := by
  intro p _ W _ m n h
  exact form_nonneg_of_disc _ _ m n h

end MPP.Solutions.Bsd133
