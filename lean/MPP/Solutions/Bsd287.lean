import Mathlib

namespace MPP.Solutions.Bsd287

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), 2 < p →
    ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2) : Polynomial (ZMod p)).coeff ((p - 1) / 2 - 1 + p) = 1 := by
  intro p _ a b hp2
  have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  have hidx : (p - 1) / 2 - 1 + p = 3 * ((p - 1) / 2) := by omega
  rw [hidx]
  have hm : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).Monic := by
    monicity!
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).natDegree = 3 := by
    compute_degree!
  have hnd : ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)) ^ ((p - 1) / 2)).natDegree = 3 * ((p - 1) / 2) := by
    rw [Polynomial.natDegree_pow, hdeg, mul_comm]
  rw [← hnd]
  exact (hm.pow _).coeff_natDegree

end MPP.Solutions.Bsd287
