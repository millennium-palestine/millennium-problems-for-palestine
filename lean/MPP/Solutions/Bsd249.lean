import Mathlib

namespace MPP.Solutions.Bsd249

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)) ^ ((p - 1) / 2)).natDegree =
      3 * ((p - 1) / 2) := by
  intro p _ a b
  have hm : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).Monic := by
    monicity!
  have hd : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)).natDegree = 3 := by
    compute_degree!
  rw [hm.natDegree_pow, hd]
  exact Nat.mul_comm _ _

end MPP.Solutions.Bsd249
