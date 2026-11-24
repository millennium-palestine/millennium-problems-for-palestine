import Mathlib

namespace MPP.Solutions.Bsd034

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K),
    (W.minimal R).HasGoodReduction R →
      ∃ a q : ℤ, 0 ≤ q ∧ W.localPolynomial R = 1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 := by
  intro R _ _ _ K _ _ _ W h
  unfold WeierstrassCurve.localPolynomial
  rw [if_pos h]
  exact ⟨_, _, Int.natCast_nonneg _, rfl⟩

end MPP.Solutions.Bsd034
