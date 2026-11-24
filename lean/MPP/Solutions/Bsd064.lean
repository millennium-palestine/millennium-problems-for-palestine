import Mathlib

namespace MPP.Solutions.Bsd064

theorem main : ∀ (p q : ℚ), (∀ e : ℚ, e ^ 3 + p * e + q ≠ 0) →
    Irreducible (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ) := by
  intro p q h
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ).natDegree = 3 := by
    compute_degree!
  have hne0 : (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial ℚ) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  apply Multiset.eq_zero_of_forall_notMem
  intro e he
  have hr := (Polynomial.mem_roots hne0).mp he
  simp [Polynomial.IsRoot] at hr
  exact h e hr

end MPP.Solutions.Bsd064
