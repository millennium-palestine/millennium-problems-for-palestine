import Mathlib

namespace MPP.Solutions.Bsd026

theorem main : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (W : WeierstrassCurve K),
    PowerSeries.constantCoeff (W.localPowerSeries R) = 1 := by
  intro R K _ _ _ _ _ _ W
  unfold WeierstrassCurve.localPowerSeries
  rw [PowerSeries.constantCoeff_invOfUnit]
  simp

end MPP.Solutions.Bsd026
