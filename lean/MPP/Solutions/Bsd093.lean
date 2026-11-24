import Mathlib

namespace MPP.Solutions.Bsd093

open scoped nonZeroDivisors

theorem main : ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n)) →
    ∃ J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K,
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x = J ^ 2 := by
  intro K _ _ x hx hev
  classical
  have hI0 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx
  -- the valuation of x is the exponential of minus the count of its principal ideal
  have key : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v.valuation K x = WithZero.exp
        (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton
          (nonZeroDivisors (NumberField.RingOfIntegers K)) x)) : ℤ) := by
    intro v
    obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (NumberField.RingOfIntegers K)) x
    have hn : n ≠ 0 := by
      rintro rfl
      apply hx
      rw [← hnd, IsLocalization.mk'_zero]
    have hd : (d : NumberField.RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (IsLocalization.mk' K n d)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            ((algebraMap (NumberField.RingOfIntegers K) K) d)⁻¹ *
          ↑(Ideal.span {n} : Ideal (NumberField.RingOfIntegers K)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      apply congr_arg
      rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
    rw [← hnd, IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hn,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hd]
    rw [← hnd] at hI0
    rw [FractionalIdeal.count_well_defined K v hI0 hI, div_eq_mul_inv, ← WithZero.exp_neg,
      ← WithZero.exp_add]
    congr 1
    ring
  choose e he using hev
  have hc : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) x) = -(2 * e v) := by
    intro v
    have h1 := key v
    rw [he v] at h1
    have h2 := WithZero.exp_injective h1
    omega
  have hfin : ∀ᶠ v in Filter.cofinite, e v = 0 := by
    filter_upwards [FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) x)] with v hv
    rw [hc v] at hv
    omega
  have hsupp : Function.HasFiniteMulSupport (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ (-(e v))) := by
    apply (Filter.eventually_cofinite.mp hfin).subset
    intro v hv h0
    apply hv
    simp [h0]
  refine ⟨∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
    (v.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ (-(e v)), ?_⟩
  rw [finprod_pow hsupp 2, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI0]
  apply finprod_congr
  intro v
  rw [← zpow_natCast, ← zpow_mul, hc v]
  congr 1
  push_cast
  ring

end MPP.Solutions.Bsd093
