import Mathlib

namespace MPP.Solutions.Bsd020

theorem finite_residueField (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Finite (IsLocalRing.ResidueField (p.adicCompletionIntegers ℚ)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm q :=
    ⟨Rat.HeightOneSpectrum.primesEquiv p, by simp⟩
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  let e := PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ) q
  have hZ : Finite (IsLocalRing.ResidueField (PadicInt (q : ℕ))) :=
    Finite.of_equiv (ZMod (q : ℕ)) (PadicInt.residueField (p := (q : ℕ))).symm.toEquiv
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv e.toAlgEquiv.toRingEquiv).toEquiv

theorem constantCoeff_localPowerSeries (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) :
    PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  unfold WeierstrassCurve.localPowerSeries
  rw [PowerSeries.constantCoeff_invOfUnit]
  simp

theorem main : ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] → ArithmeticFunction.IsMultiplicative (WeierstrassCurve.LFunction E) := by
  intro E _
  unfold WeierstrassCurve.LFunction
  apply ArithmeticFunction.isMultiplicative_eulerProduct
  intro p
  unfold WeierstrassCurve.localEulerFactor
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
  · haveI := finite_residueField p
    haveI := Fintype.ofFinite (IsLocalRing.ResidueField (p.adicCompletionIntegers ℚ))
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card _
  · exact constantCoeff_localPowerSeries _ _ _

end MPP.Solutions.Bsd020
