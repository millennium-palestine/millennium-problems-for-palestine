import Mathlib

namespace MPP.Solutions.Bsd025

theorem main : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
    Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers ℚ)) := by
  intro p
  obtain ⟨q, rfl⟩ : ∃ q, p = (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q :=
    ⟨Rat.HeightOneSpectrum.primesEquiv p, by simp⟩
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  let e := PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) q
  have hZ : Finite (IsLocalRing.ResidueField (PadicInt (q : ℕ))) :=
    Finite.of_equiv (ZMod (q : ℕ)) (PadicInt.residueField (p := (q : ℕ))).symm.toEquiv
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv e.toAlgEquiv.toRingEquiv).toEquiv

end MPP.Solutions.Bsd025
