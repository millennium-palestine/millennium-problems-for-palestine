import Mathlib

namespace MPP.Solutions.Bsd286

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p) (n : ℕ), (p - 1) / 2 ≤ n →
    ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2) : Polynomial (ZMod p)).coeff (n + p) = 0 := by
  intro p hp a b n hn
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).natDegree ≤ 3 := by
    compute_degree!
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc _ ≤ (p - 1) / 2 * (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).natDegree :=
        Polynomial.natDegree_pow_le
    _ ≤ (p - 1) / 2 * 3 := Nat.mul_le_mul_left _ hdeg
    _ < n + p := by omega

end MPP.Solutions.Bsd286
