import Mathlib
import MPP.Solutions.Bsd026
import MPP.Solutions.Bsd095
import MPP.Solutions.Bsd097
import MPP.Solutions.Bsd098
import MPP.Solutions.Bsd099

namespace MPP.Solutions.Bsd102

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (k : ℕ),
    E.LFunction (Rat.HeightOneSpectrum.natGenerator v ^ k) =
      PowerSeries.coeff k ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)) := by
  intro E _ v k
  have hp : (Rat.HeightOneSpectrum.natGenerator v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  -- the local factor at w is ofPowerSeries of its residue cardinality, which is natGenerator w
  have hloc : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (E.baseChange (w.adicCompletion ℚ)).localEulerFactor (w.adicCompletionIntegers ℚ) =
        ArithmeticFunction.ofPowerSeries (Rat.HeightOneSpectrum.natGenerator w)
          ((E.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ)) := by
    intro w
    rw [WeierstrassCurve.localEulerFactor, MPP.Solutions.Bsd099.main w]
  have hconst : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      PowerSeries.constantCoeff ((E.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ)) = 1 :=
    fun w => MPP.Solutions.Bsd026.main _ _ _
  have hE : E.LFunction = ArithmeticFunction.eulerProduct (fun w : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => (E.baseChange (w.adicCompletion ℚ)).localEulerFactor
        (w.adicCompletionIntegers ℚ)) := rfl
  -- the other factors are trivial at p^j, j ≤ k
  have hyp1 : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), w ≠ v → ∀ j, j ≤ k →
      (E.baseChange (w.adicCompletion ℚ)).localEulerFactor (w.adicCompletionIntegers ℚ)
        (Rat.HeightOneSpectrum.natGenerator v ^ j) =
        (1 : ArithmeticFunction ℤ) (Rat.HeightOneSpectrum.natGenerator v ^ j) := by
    intro w hw j hj
    rw [hloc w]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [ArithmeticFunction.ofPowerSeries_apply_one, hconst w]
    · have hq : Nat.Prime (Rat.HeightOneSpectrum.natGenerator w) := Rat.HeightOneSpectrum.prime_natGenerator w
      have hne : Rat.HeightOneSpectrum.natGenerator w ≠ Rat.HeightOneSpectrum.natGenerator v :=
        fun h => hw ((Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).injective
          (Subtype.ext h))
      have hndvd : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ Rat.HeightOneSpectrum.natGenerator w := fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
      rw [MPP.Solutions.Bsd097.main _ _ _ _ hq.one_lt hp hndvd hj0,
        ArithmeticFunction.one_apply_ne (ne_of_gt (Nat.one_lt_pow hj0.ne' hp.one_lt))]
  -- for each n, all but finitely many factors have value 1 at n
  have hyp2 : ∀ n : ℕ, Filter.Eventually (fun w : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => (E.baseChange (w.adicCompletion ℚ)).localEulerFactor
        (w.adicCompletionIntegers ℚ) n = (1 : ArithmeticFunction ℤ) n) Filter.cofinite := by
    intro n
    rw [Filter.eventually_cofinite]
    apply (MPP.Solutions.Bsd098.main n).subset
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    by_contra hlt
    replace hlt := not_le.mp hlt
    apply hw
    rw [hloc w]
    rcases n with _ | _ | n
    · simp
    · simp [ArithmeticFunction.ofPowerSeries_apply_one, hconst w]
    · have hq : 1 < Rat.HeightOneSpectrum.natGenerator w := by omega
      rw [ArithmeticFunction.ofPowerSeries_apply hq,
        ArithmeticFunction.one_apply_ne (by omega : n + 1 + 1 ≠ 1)]
      rw [Function.extend_apply' _ _ _ ?_, Pi.zero_apply]
      rintro ⟨j, hj⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp at hj
      · have := Nat.le_self_pow hj0.ne' (Rat.HeightOneSpectrum.natGenerator w)
        omega
  rw [hE, MPP.Solutions.Bsd095.main (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (fun w => (E.baseChange (w.adicCompletion ℚ)).localEulerFactor (w.adicCompletionIntegers ℚ)) v
    (Rat.HeightOneSpectrum.natGenerator v) k hp hyp1 hyp2, hloc v,
    ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt]

end MPP.Solutions.Bsd102
