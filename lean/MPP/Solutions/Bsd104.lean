import Mathlib
import MPP.Solutions.Bsd021
import MPP.Solutions.Bsd029
import MPP.Solutions.Bsd033
import MPP.Solutions.Bsd045
import MPP.Solutions.Bsd099
import MPP.Solutions.Bsd102

namespace MPP.Solutions.Bsd104

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (a q : ℤ),
      ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
          (v.adicCompletionIntegers ℚ) →
        (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
          1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 →
        a ^ 2 ≤ 4 * q) →
    ∀ n : ℕ, 0 < n → ‖((E.LFunction n : ℤ) : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
  intro E _ hH
  refine MPP.Solutions.Bsd045.main E ?_
  intro p k hp
  set v := (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm ⟨p, hp⟩ with hvdef
  have hv : Rat.HeightOneSpectrum.natGenerator v = p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply
      ⟨p, hp⟩)
  have hcoeff := MPP.Solutions.Bsd102.main E v k
  rw [hv] at hcoeff
  rw [hcoeff, MPP.Solutions.Bsd021.main p k hp]
  have hpk : (1 : ℝ) ≤ ((k : ℝ) + 1) * Real.sqrt ((p : ℝ) ^ k) := by
    have h1 : (1 : ℝ) ≤ Real.sqrt ((p : ℝ) ^ k) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (one_le_pow₀ (by exact_mod_cast hp.one_lt.le))
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  by_cases hg : ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
      (v.adicCompletionIntegers ℚ)
  · -- good reduction: the local polynomial has the shape 1 - a T + q T² with q the residue cardinality
    have hshape : ∃ a : ℤ, (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
        1 - Polynomial.C a * Polynomial.X +
          Polynomial.C ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℕ) : ℤ) *
            Polynomial.X ^ 2 := by
      refine ⟨(Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℤ) + 1 -
        (Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).reduction
          (v.adicCompletionIntegers ℚ)).toAffine.Point : ℤ), ?_⟩
      rw [WeierstrassCurve.localPolynomial]
      simp only [hg, if_true]
    obtain ⟨a, ha⟩ := hshape
    have hq : ((Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℕ) : ℤ) = (p : ℤ) := by
      rw [MPP.Solutions.Bsd099.main v, hv]
    rw [hq] at ha
    have hsq : a ^ 2 ≤ 4 * (p : ℤ) := hH v a (p : ℤ) hg ha
    have hc := MPP.Solutions.Bsd033.main a (p : ℤ) (by positivity) hsq k
    have hcoeff' : PowerSeries.coeff k ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
        (v.adicCompletionIntegers ℚ)) ^ 2 ≤ ((k : ℤ) + 1) ^ 2 * (p : ℤ) ^ k := by
      rw [WeierstrassCurve.localPowerSeries, ha]
      exact hc
    have hb : 0 ≤ ((k : ℝ) + 1) * Real.sqrt ((p : ℝ) ^ k) := by positivity
    have hsqR : (((PowerSeries.coeff k ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
        (v.adicCompletionIntegers ℚ)) : ℤ) : ℝ)) ^ 2 ≤ (((k : ℝ) + 1) * Real.sqrt ((p : ℝ) ^ k)) ^ 2 := by
      have h2 : ((PowerSeries.coeff k ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
          (v.adicCompletionIntegers ℚ)) ^ 2 : ℤ) : ℝ) ≤ ((((k : ℤ) + 1) ^ 2 * (p : ℤ) ^ k : ℤ) : ℝ) := by
        exact_mod_cast hcoeff'
      push_cast at h2
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      linarith
    rw [Complex.norm_intCast]
    push_cast
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsqR hb)
  · -- bad reduction: the coefficients have absolute value at most 1
    have hb := MPP.Solutions.Bsd029.main (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (E.baseChange (v.adicCompletion ℚ)) hg k
    have h1 : |((PowerSeries.coeff k ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
        (v.adicCompletionIntegers ℚ)) : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast hb
    rw [Complex.norm_intCast]
    push_cast
    linarith

end MPP.Solutions.Bsd104
