import Mathlib
import MPP.Solutions.Bsd166

namespace MPP.Solutions.Bsd181

theorem main : ∀ (p : ℕ) [Fact p.Prime] (j k : ℕ) (h : Polynomial (ZMod p)) (x : ZMod p), 0 < k → k < p →
    (Polynomial.hasseDeriv k (Polynomial.X ^ (p * j) * h)).eval x =
      x ^ j * (Polynomial.hasseDeriv k h).eval x := by
  intro p _ j k h x hk0 hkp
  rw [MPP.Solutions.Bsd166.main p (ZMod p) j k h hk0 hkp, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, pow_mul, ZMod.pow_card]

end MPP.Solutions.Bsd181
