import Mathlib

namespace MPP.Solutions.Bsd372

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p) (i t : ℕ), t ≤ i →
    ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2)).coeff
      ((p - 1) / 2 + (i - t) + p) = 0 := by
  intro p _ a b i t _
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcubic : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b :
      Polynomial (ZMod p)).natDegree ≤ 3 := by
    compute_degree!
  have hdeg : ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^
      ((p - 1) / 2)).natDegree ≤ 3 * ((p - 1) / 2) := by
    calc _ ≤ (p - 1) / 2 * (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X +
          Polynomial.C b : Polynomial (ZMod p)).natDegree := Polynomial.natDegree_pow_le
      _ ≤ (p - 1) / 2 * 3 := Nat.mul_le_mul_left _ hcubic
      _ = 3 * ((p - 1) / 2) := Nat.mul_comm _ _
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  omega

end MPP.Solutions.Bsd372
