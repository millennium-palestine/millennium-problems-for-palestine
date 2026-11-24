import Mathlib

namespace MPP.Solutions.Bsd032

-- the degree form at m = a, n = 2 gives a² ≤ 4p, as in bsd-031
theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    (∀ m n : ℤ, 0 ≤ m ^ 2 - ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) * m * n + (p : ℤ) * n ^ 2) →
      |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p _ W _ h
  have key := h ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) 2
  have hsq : ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) ^ 2 ≤ 4 * (p : ℤ) := by
    nlinarith [key]
  have hsqR : ((p : ℝ) + 1 - ((Nat.card W.toAffine.Point : ℕ) : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast hsq
  have h4 : (2 : ℝ) * Real.sqrt (p : ℝ) = Real.sqrt (4 * (p : ℝ)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 from by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [h4, abs_sub_comm]
  exact Real.abs_le_sqrt hsqR

end MPP.Solutions.Bsd032
