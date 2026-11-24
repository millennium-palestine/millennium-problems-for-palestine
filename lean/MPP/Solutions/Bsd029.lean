import Mathlib

namespace MPP.Solutions.Bsd029

-- the inverse of 1 − u X in ℤ⟦X⟧ has coefficients uᵏ, so |coefficients| ≤ 1 when |u| ≤ 1
theorem coeff_invOfUnit_le (f : PowerSeries ℤ) (u : ℤ) (hu : |u| ≤ 1)
    (hf : f = 1 - PowerSeries.C u * PowerSeries.X) (k : ℕ) :
    |PowerSeries.coeff k (PowerSeries.invOfUnit f 1)| ≤ 1 := by
  have h0 : PowerSeries.constantCoeff f = ((1 : ℤˣ) : ℤ) := by
    simp [hf]
  have hh : f * PowerSeries.invOfUnit f 1 = 1 := by
    simpa using PowerSeries.mul_invOfUnit f 1 h0
  have hg : f * PowerSeries.mk (fun n => u ^ n) = 1 := by
    rw [hf]
    ext n
    rcases n with _ | n
    · simp
    · simp only [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      simp [pow_succ]
      ring
  have heq : PowerSeries.invOfUnit f 1 = PowerSeries.mk (fun n => u ^ n) := by
    linear_combination (PowerSeries.mk fun n => u ^ n) * hh - PowerSeries.invOfUnit f 1 * hg
  rw [heq, PowerSeries.coeff_mk, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) hu

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K]
    [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K),
    ¬ (W.minimal R).HasGoodReduction R →
      ∀ k : ℕ, |PowerSeries.coeff k (W.localPowerSeries R)| ≤ 1 := by
  intro R _ _ _ K _ _ _ W hbad k
  -- without good reduction the local polynomial is 1 − X, 1 + X or 1
  have hP : W.localPolynomial R = 1 - Polynomial.X ∨ W.localPolynomial R = 1 + Polynomial.X ∨
      W.localPolynomial R = 1 := by
    unfold WeierstrassCurve.localPolynomial
    split_ifs
    all_goals first
      | exact absurd (by assumption) hbad
      | (left; rfl)
      | (right; left; rfl)
      | (right; right; rfl)
  unfold WeierstrassCurve.localPowerSeries
  rcases hP with h | h | h
  · rw [h]
    exact coeff_invOfUnit_le _ 1 (by norm_num) (by simp) k
  · rw [h]
    exact coeff_invOfUnit_le _ (-1) (by norm_num) (by simp) k
  · rw [h]
    exact coeff_invOfUnit_le _ 0 (by norm_num) (by simp) k

end MPP.Solutions.Bsd029
