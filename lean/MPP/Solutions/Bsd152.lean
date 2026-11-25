import Mathlib
import MPP.Solutions.Bsd141
import MPP.Solutions.Bsd151

namespace MPP.Solutions.Bsd152

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p)
    [(WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).IsElliptic], p ≠ 2 →
    (2 : ℤ) ∣ ((Nat.card (WeierstrassCurve.mk (0 : ZMod p) 0 0 a b).toAffine.Point : ℕ) : ℤ) -
      (1 + ((Finset.univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)) := by
  intro p _ a b _ hp
  have alg : ∀ S R : ℤ, (2 : ℤ) ∣ S - ((p : ℤ) - R) →
      (2 : ℤ) ∣ ((p : ℤ) + 1 + S) - (1 + R) := by
    intro S R h
    have e : ((p : ℤ) + 1 + S) - (1 + R) = (S - ((p : ℤ) - R)) + 2 * ((p : ℤ) - R) := by ring
    rw [e]
    exact dvd_add h (dvd_mul_right 2 _)
  rw [MPP.Solutions.Bsd141.main p a b hp]
  exact alg _ _ (MPP.Solutions.Bsd151.main p a b)

end MPP.Solutions.Bsd152
