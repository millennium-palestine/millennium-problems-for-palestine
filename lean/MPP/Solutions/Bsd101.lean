import Mathlib

namespace MPP.Solutions.Bsd101

-- a fixed nonzero integer lies in finitely many primes
theorem finite_mem (K : Type) [Field K] [NumberField K] (r : NumberField.RingOfIntegers K) (hr : r ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | r ∈ v.asIdeal}.Finite := by
  have hne : Ideal.span ({r} : Set (NumberField.RingOfIntegers K)) ≠ ⊥ :=
    fun h => hr (Ideal.span_singleton_eq_bot.mp h)
  refine (Ideal.finite_factors hne).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)

-- a = r / s: the valuation of a times that of s is the valuation of r
theorem val_mul_den (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (r s : NumberField.RingOfIntegers K)
    (a : K) (hs : s ∈ nonZeroDivisors (NumberField.RingOfIntegers K))
    (ha : IsLocalization.mk' K r ⟨s, hs⟩ = a) :
    v.valuation K a * v.valuation K (algebraMap (NumberField.RingOfIntegers K) K s) =
      v.valuation K (algebraMap (NumberField.RingOfIntegers K) K r) := by
  rw [← ha, ← map_mul, IsLocalization.mk'_spec]

-- finitely many primes at which a has valuation above 1
theorem finite_gt (K : Type) [Field K] [NumberField K] (a : K) :
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | 1 < v.valuation K a}.Finite := by
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (NumberField.RingOfIntegers K)) a
  refine (finite_mem K (s : NumberField.RingOfIntegers K) (nonZeroDivisors.coe_ne_zero s)).subset ?_
  intro v hv
  have key := val_mul_den K v r (s : NumberField.RingOfIntegers K) a s.2 hrs
  have hr1 := v.valuation_le_one (K := K) r
  have hs1 := v.valuation_le_one (K := K) (s : NumberField.RingOfIntegers K)
  have hslt : v.valuation K (algebraMap (NumberField.RingOfIntegers K) K s) < 1 := by
    by_contra hcon
    have h1 : 1 ≤ v.valuation K (algebraMap (NumberField.RingOfIntegers K) K s) := not_lt.mp hcon
    have h1' : v.valuation K (algebraMap (NumberField.RingOfIntegers K) K s) = 1 := le_antisymm hs1 h1
    rw [h1', mul_one] at key
    have h2 : 1 < v.valuation K (algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [← key]
      exact hv
    exact absurd (lt_of_lt_of_le h2 hr1) (lt_irrefl _)
  exact (v.valuation_lt_one_iff_mem s).mp hslt

-- finitely many primes at which a nonzero a has valuation below 1
theorem finite_lt (K : Type) [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) | v.valuation K a < 1}.Finite := by
  obtain ⟨r, s, hrs⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (NumberField.RingOfIntegers K)) a
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply ha
    rw [← hrs, IsLocalization.mk'_zero]
  refine (finite_mem K r hr0).subset ?_
  intro v hv
  have key := val_mul_den K v r (s : NumberField.RingOfIntegers K) a s.2 hrs
  have hs1 := v.valuation_le_one (K := K) (s : NumberField.RingOfIntegers K)
  have hr_lt : v.valuation K (algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
    rw [← key]
    calc v.valuation K a * v.valuation K (algebraMap (NumberField.RingOfIntegers K) K s)
        ≤ v.valuation K a * 1 := mul_le_mul_right hs1 _
      _ = v.valuation K a := mul_one _
      _ < 1 := hv
  exact (v.valuation_lt_one_iff_mem r).mp hr_lt

theorem main : ∀ (p q : ℚ) (f : Polynomial ℚ) [Fact (Irreducible f)],
    f = Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q →
    ∃ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (AdjoinRoot f))),
      S.Finite ∧ ∀ x y : ℚ, y ^ 2 = x ^ 3 + p * x + q →
        algebraMap ℚ (AdjoinRoot f) x ≠ AdjoinRoot.root f →
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (AdjoinRoot f)), v ∉ S →
          ∃ n : ℤ, v.valuation (AdjoinRoot f) (algebraMap ℚ (AdjoinRoot f) x - AdjoinRoot.root f) =
            WithZero.exp (2 * n) := by
  intro p q f _ hf
  have hf0 : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root f
  have hθ : AdjoinRoot.root f ^ 3 + algebraMap ℚ (AdjoinRoot f) p * AdjoinRoot.root f +
      algebraMap ℚ (AdjoinRoot f) q = 0 := by
    have h : Polynomial.aeval (AdjoinRoot.root f)
        (Polynomial.X ^ 3 + Polynomial.C p * Polynomial.X + Polynomial.C q) = 0 := by
      rw [← hf]
      exact hf0
    simpa using h
  have hD' : Polynomial.derivative f = Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C p := by
    rw [hf]
    simp only [map_add, Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X,
      Polynomial.derivative_C]
    norm_num
  have hder : 3 * AdjoinRoot.root f ^ 2 + algebraMap ℚ (AdjoinRoot f) p ≠ 0 := by
    intro h0
    obtain ⟨a, b, hab⟩ := (Polynomial.separable_def f).mp (Irreducible.separable Fact.out)
    have h2 := congrArg (Polynomial.aeval (AdjoinRoot.root f)) hab
    simp [hf0, hD'] at h2
    simp at h0
    simp [h0] at h2
  refine ⟨({v | 1 < v.valuation (AdjoinRoot f) (AdjoinRoot.root f)} ∪
      {v | 1 < v.valuation (AdjoinRoot f) (algebraMap ℚ (AdjoinRoot f) p)}) ∪
      {v | v.valuation (AdjoinRoot f) (3 * AdjoinRoot.root f ^ 2 + algebraMap ℚ (AdjoinRoot f) p) < 1},
    ((finite_gt _ _).union (finite_gt _ _)).union (finite_lt _ _ hder), ?_⟩
  intro x y hxy hne v hv
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hv
  obtain ⟨⟨hθ1, hP1⟩, hD1⟩ := hv
  set θ := AdjoinRoot.root f with hθdef
  set P := algebraMap ℚ (AdjoinRoot f) p with hPdef
  set xL := algebraMap ℚ (AdjoinRoot f) x with hxdef
  set yL := algebraMap ℚ (AdjoinRoot f) y with hydef
  set w := v.valuation (AdjoinRoot f) with hwdef
  have hyL : yL ^ 2 = xL ^ 3 + P * xL + algebraMap ℚ (AdjoinRoot f) q := by
    have h := congrArg (algebraMap ℚ (AdjoinRoot f)) hxy
    simpa only [map_add, map_mul, map_pow] using h
  have hαβ : (xL - θ) * (xL ^ 2 + xL * θ + θ ^ 2 + P) = yL ^ 2 := by
    linear_combination (-1 : AdjoinRoot f) * hθ + (-1 : AdjoinRoot f) * hyL
  have hαw : w (xL - θ) ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  have h2le : w 2 ≤ 1 := by
    have e : (2 : AdjoinRoot f) = algebraMap (NumberField.RingOfIntegers (AdjoinRoot f)) (AdjoinRoot f) 2 :=
      (map_ofNat _ 2).symm
    rw [e]
    exact v.valuation_le_one (K := AdjoinRoot f) 2
  have hDeq : 3 * θ ^ 2 + P = (xL ^ 2 + xL * θ + θ ^ 2 + P) - (xL - θ) * (xL + 2 * θ) := by ring
  by_cases h1 : w (xL - θ) = 1
  · exact ⟨0, by rw [h1]; simp⟩
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- the case v(x - θ) < 1: the factor β has valuation exactly 1
    have hxle : w xL ≤ 1 := by
      have h := Valuation.map_add w (xL - θ) θ
      rw [sub_add_cancel] at h
      exact h.trans (max_le hlt.le hθ1)
    have hxθ2 : w (xL + 2 * θ) ≤ 1 := by
      refine (Valuation.map_add w xL (2 * θ)).trans (max_le hxle ?_)
      rw [map_mul]
      exact (mul_le_mul' h2le hθ1).trans (le_of_eq (one_mul 1))
    have hβle : w (xL ^ 2 + xL * θ + θ ^ 2 + P) ≤ 1 := by
      have hA : w (xL ^ 2) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one₀ (zero_le') hxle
      have hB : w (xL * θ) ≤ 1 := by
        rw [map_mul]
        exact (mul_le_mul' hxle hθ1).trans (le_of_eq (one_mul 1))
      have hC : w (θ ^ 2) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one₀ (zero_le') hθ1
      refine (Valuation.map_add w _ P).trans (max_le ?_ hP1)
      refine (Valuation.map_add w _ _).trans (max_le ?_ hC)
      exact (Valuation.map_add w _ _).trans (max_le hA hB)
    have hαx : w ((xL - θ) * (xL + 2 * θ)) < 1 := by
      rw [map_mul]
      calc w (xL - θ) * w (xL + 2 * θ) ≤ w (xL - θ) * 1 := mul_le_mul_right hxθ2 _
        _ = w (xL - θ) := mul_one _
        _ < 1 := hlt
    have hβ1 : w (xL ^ 2 + xL * θ + θ ^ 2 + P) = 1 := by
      apply le_antisymm hβle
      by_contra hcon
      have hβlt : w (xL ^ 2 + xL * θ + θ ^ 2 + P) < 1 := not_le.mp hcon
      have hDlt : w (3 * θ ^ 2 + P) < 1 := by
        rw [hDeq]
        exact lt_of_le_of_lt (Valuation.map_sub w _ _) (max_lt hβlt hαx)
      exact absurd hD1 (not_le.mpr hDlt)
    have hsq : w (xL - θ) * w (xL ^ 2 + xL * θ + θ ^ 2 + P) = w yL ^ 2 := by
      rw [← map_mul, hαβ, map_pow]
    rw [hβ1, mul_one] at hsq
    have hyne : w yL ≠ 0 := by
      intro h0
      rw [h0] at hsq
      exact hαw (by rw [hsq]; simp)
    obtain ⟨c, hc⟩ : ∃ c : ℤ, w yL = WithZero.exp c := ⟨_, (WithZero.exp_log hyne).symm⟩
    refine ⟨c, ?_⟩
    rw [hsq, hc, sq, ← WithZero.exp_add]
    congr 1
    ring
  · -- the case v(x - θ) > 1: then v(x - θ) = v(x) and v(β) = v(x)², so v(x) has even exponent
    have hxgt : 1 < w xL := by
      by_contra hcon
      have hxle : w xL ≤ 1 := not_lt.mp hcon
      have h := Valuation.map_sub w xL θ
      exact absurd (lt_of_lt_of_le hgt (h.trans (max_le hxle hθ1))) (lt_irrefl _)
    have hα_eq : w (xL - θ) = w xL :=
      Valuation.map_sub_eq_of_lt_left w (lt_of_le_of_lt hθ1 hxgt)
    have hrest : w (xL * θ + θ ^ 2 + P) < w (xL ^ 2) := by
      rw [map_pow]
      have h1' : w (xL * θ) ≤ w xL := by
        rw [map_mul]
        exact mul_le_of_le_one_right' hθ1
      have h2' : w (θ ^ 2) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one₀ (zero_le') hθ1
      have h3: w (xL * θ + θ ^ 2 + P) ≤ w xL :=
        (Valuation.map_add w _ P).trans
          (max_le ((Valuation.map_add w _ _).trans (max_le h1' (h2'.trans hxgt.le))) (hP1.trans hxgt.le))
      calc w (xL * θ + θ ^ 2 + P) ≤ w xL := h3
        _ < w xL * w xL := lt_mul_of_one_lt_right (zero_lt_one.trans hxgt) hxgt
        _ = w xL ^ 2 := (sq _).symm
    have hβ_eq : w (xL ^ 2 + xL * θ + θ ^ 2 + P) = w xL ^ 2 := by
      rw [show xL ^ 2 + xL * θ + θ ^ 2 + P = xL ^ 2 + (xL * θ + θ ^ 2 + P) by ring]
      exact (Valuation.map_add_eq_of_lt_left w hrest).trans (by rw [map_pow])
    have hsq : w (xL - θ) * w (xL ^ 2 + xL * θ + θ ^ 2 + P) = w yL ^ 2 := by
      rw [← map_mul, hαβ, map_pow]
    rw [hα_eq, hβ_eq] at hsq
    have hxne : w xL ≠ 0 := by
      intro h0
      rw [h0] at hxgt
      simp at hxgt
    obtain ⟨m, hm⟩ : ∃ m : ℤ, w xL = WithZero.exp m := ⟨_, (WithZero.exp_log hxne).symm⟩
    have hyne : w yL ≠ 0 := by
      intro h0
      rw [h0] at hsq
      simp [hxne] at hsq
    obtain ⟨c, hc⟩ : ∃ c : ℤ, w yL = WithZero.exp c := ⟨_, (WithZero.exp_log hyne).symm⟩
    rw [hm, hc] at hsq
    have e1 : WithZero.exp m * WithZero.exp m ^ 2 = WithZero.exp (3 * m) := by
      rw [sq, ← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      ring
    have e2 : WithZero.exp c ^ 2 = WithZero.exp (2 * c) := by
      rw [sq, ← WithZero.exp_add]
      congr 1
      ring
    rw [e1, e2] at hsq
    have h3 : 3 * m = 2 * c := WithZero.exp_injective hsq
    refine ⟨c - m, ?_⟩
    rw [hα_eq, hm]
    congr 1
    omega

end MPP.Solutions.Bsd101
