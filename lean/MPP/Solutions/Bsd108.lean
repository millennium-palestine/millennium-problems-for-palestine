import Mathlib

namespace MPP.Solutions.Bsd108

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

theorem main : ∀ (p e : ℚ) (g : Polynomial ℚ) [Fact (Irreducible g)],
    g = Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p) →
    ∃ S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (AdjoinRoot g))),
      S.Finite ∧ ∀ x y : ℚ, y ^ 2 = (x - e) * (x ^ 2 + e * x + (e ^ 2 + p)) →
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (AdjoinRoot g)), v ∉ S →
          ∃ n : ℤ, v.valuation (AdjoinRoot g) (algebraMap ℚ (AdjoinRoot g) x - AdjoinRoot.root g) =
            WithZero.exp (2 * n) := by
  intro p e g hI hg
  have hirr : Irreducible g := hI.out
  have hg0 : Polynomial.aeval (AdjoinRoot.root g) g = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root g
  have hθ : AdjoinRoot.root g ^ 2 + algebraMap ℚ (AdjoinRoot g) e * AdjoinRoot.root g +
      (algebraMap ℚ (AdjoinRoot g) e ^ 2 + algebraMap ℚ (AdjoinRoot g) p) = 0 := by
    have h : Polynomial.aeval (AdjoinRoot.root g)
        (Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C (e ^ 2 + p)) = 0 := by
      rw [← hg]
      exact hg0
    simpa [map_add, map_pow] using h
  -- g has no rational root, since it is irreducible of degree 2
  have hnot : ∀ r : ℚ, r ^ 2 + e * r + (e ^ 2 + p) ≠ 0 := by
    intro r hr
    have hgr : g.IsRoot r := by
      rw [Polynomial.IsRoot.def, hg]
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      exact hr
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr hgr
    have hdeg : g.degree = 2 := by
      rw [hg]
      compute_degree!
    rw [hdeg] at h1
    exact absurd h1 (by decide)
  -- the root is not rational
  have hrootL : ∀ r : ℚ, AdjoinRoot.root g ≠ algebraMap ℚ (AdjoinRoot g) r := by
    intro r hr
    apply hnot r
    have h : algebraMap ℚ (AdjoinRoot g) (r ^ 2 + e * r + (e ^ 2 + p)) = 0 := by
      rw [hr] at hθ
      simp only [map_add, map_mul, map_pow]
      linear_combination hθ
    exact (map_eq_zero_iff _ (algebraMap ℚ (AdjoinRoot g)).injective).mp h
  have hD0 : 2 * AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) e ≠ 0 := by
    intro h0
    apply hrootL (-(e / 2))
    simp only [map_neg, map_div₀, map_ofNat]
    linear_combination h0 / 2
  refine ⟨({v | 1 < v.valuation (AdjoinRoot g) (AdjoinRoot.root g)} ∪
      {v | 1 < v.valuation (AdjoinRoot g) (algebraMap ℚ (AdjoinRoot g) e)}) ∪
      ({v | v.valuation (AdjoinRoot g) (AdjoinRoot.root g - algebraMap ℚ (AdjoinRoot g) e) < 1} ∪
      {v | v.valuation (AdjoinRoot g) (2 * AdjoinRoot.root g + algebraMap ℚ (AdjoinRoot g) e) < 1}),
    ((finite_gt _ _).union (finite_gt _ _)).union
      ((finite_lt _ _ (sub_ne_zero.mpr (hrootL e))).union (finite_lt _ _ hD0)), ?_⟩
  intro x y hxy v hv
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hv
  obtain ⟨⟨hθ1, he1⟩, hET, hD1⟩ := hv
  set θ := AdjoinRoot.root g with hθdef
  set eL := algebraMap ℚ (AdjoinRoot g) e with heLdef
  set xL := algebraMap ℚ (AdjoinRoot g) x with hxdef
  set yL := algebraMap ℚ (AdjoinRoot g) y with hydef
  set w := v.valuation (AdjoinRoot g) with hwdef
  have hyL : yL ^ 2 = (xL - eL) * (xL ^ 2 + eL * xL + (eL ^ 2 + algebraMap ℚ (AdjoinRoot g) p)) := by
    have h := congrArg (algebraMap ℚ (AdjoinRoot g)) hxy
    simpa only [map_add, map_mul, map_pow, map_sub] using h
  -- the identity α β c = y², with α = x − θ, β = x + e + θ, c = x − e
  have hαβc : (xL - θ) * (xL + eL + θ) * (xL - eL) = yL ^ 2 := by
    linear_combination (-(xL - eL)) * hθ - hyL
  have hαne : xL - θ ≠ 0 := sub_ne_zero.mpr (hrootL x).symm
  have hαw : w (xL - θ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hαne
  have h2le : w 2 ≤ 1 := by
    have e2 : (2 : AdjoinRoot g) = algebraMap (NumberField.RingOfIntegers (AdjoinRoot g)) (AdjoinRoot g) 2 :=
      (map_ofNat _ 2).symm
    rw [e2]
    exact v.valuation_le_one (K := AdjoinRoot g) 2
  have hDle : w (2 * θ + eL) ≤ 1 := by
    refine (Valuation.map_add w _ _).trans (max_le ?_ he1)
    rw [map_mul]
    exact (mul_le_mul' h2le hθ1).trans (le_of_eq (one_mul 1))
  have hDw : w (2 * θ + eL) = 1 := le_antisymm hDle hD1
  have hZle : w (θ - eL) ≤ 1 := (Valuation.map_sub w _ _).trans (max_le hθ1 he1)
  have hZw : w (θ - eL) = 1 := le_antisymm hZle hET
  by_cases h1 : w (xL - θ) = 1
  · exact ⟨0, by rw [h1]; simp⟩
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · -- v(x − θ) < 1: then v(β) = 1 and v(x − e) = 1, so v(x − θ) = v(y)²
    have hβeq : xL + eL + θ = (xL - θ) + (2 * θ + eL) := by ring
    have hlt2 : w (xL - θ) < w (2 * θ + eL) := by
      rw [hDw]
      exact hlt
    have hwβ : w (xL + eL + θ) = 1 := by
      rw [hβeq, Valuation.map_add_eq_of_lt_right w hlt2]
      exact hDw
    have hceq : xL - eL = (xL - θ) + (θ - eL) := by ring
    have hlt3 : w (xL - θ) < w (θ - eL) := by
      rw [hZw]
      exact hlt
    have hwc : w (xL - eL) = 1 := by
      rw [hceq, Valuation.map_add_eq_of_lt_right w hlt3]
      exact hZw
    have hsq : w (xL - θ) * w (xL + eL + θ) * w (xL - eL) = w yL ^ 2 := by
      rw [← map_mul, ← map_mul, hαβc, map_pow]
    rw [hwβ, hwc, mul_one, mul_one] at hsq
    have hyne : w yL ≠ 0 := by
      intro h0
      rw [h0] at hsq
      exact hαw (by rw [hsq]; simp)
    obtain ⟨c, hc⟩ : ∃ c : ℤ, w yL = WithZero.exp c := ⟨_, (WithZero.exp_log hyne).symm⟩
    refine ⟨c, ?_⟩
    rw [hsq, hc, sq, ← WithZero.exp_add]
    congr 1
    ring
  · -- v(x − θ) > 1: then v(x) = v(x − θ) = v(x + e + θ) = v(x − e), and 3m = 2k
    have hxgt : 1 < w xL := by
      by_contra hcon
      have hxle : w xL ≤ 1 := not_lt.mp hcon
      have h := Valuation.map_sub w xL θ
      exact absurd (lt_of_lt_of_le hgt (h.trans (max_le hxle hθ1))) (lt_irrefl _)
    have hα_eq : w (xL - θ) = w xL := Valuation.map_sub_eq_of_lt_left w (lt_of_le_of_lt hθ1 hxgt)
    have hβ_eq : w (xL + eL + θ) = w xL := by
      have hlt4 : w (eL + θ) < w xL :=
        lt_of_le_of_lt ((Valuation.map_add w _ _).trans (max_le he1 hθ1)) hxgt
      rw [show xL + eL + θ = xL + (eL + θ) by ring]
      exact Valuation.map_add_eq_of_lt_left w hlt4
    have hc_eq : w (xL - eL) = w xL := Valuation.map_sub_eq_of_lt_left w (lt_of_le_of_lt he1 hxgt)
    have hsq : w (xL - θ) * w (xL + eL + θ) * w (xL - eL) = w yL ^ 2 := by
      rw [← map_mul, ← map_mul, hαβc, map_pow]
    rw [hα_eq, hβ_eq, hc_eq] at hsq
    have hxne : w xL ≠ 0 := by
      intro h0
      rw [h0] at hxgt
      simp at hxgt
    have hyne : w yL ≠ 0 := by
      intro h0
      rw [h0] at hsq
      simp [hxne] at hsq
    obtain ⟨m, hm⟩ : ∃ m : ℤ, w xL = WithZero.exp m := ⟨_, (WithZero.exp_log hxne).symm⟩
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w yL = WithZero.exp k := ⟨_, (WithZero.exp_log hyne).symm⟩
    rw [hm, hk] at hsq
    have e1 : WithZero.exp m * WithZero.exp m * WithZero.exp m = WithZero.exp (3 * m) := by
      rw [← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      ring
    have e2 : WithZero.exp k ^ 2 = WithZero.exp (2 * k) := by
      rw [sq, ← WithZero.exp_add]
      congr 1
      ring
    rw [e1, e2] at hsq
    have h3 : 3 * m = 2 * k := WithZero.exp_injective hsq
    refine ⟨k - m, ?_⟩
    rw [hα_eq, hm]
    congr 1
    omega

end MPP.Solutions.Bsd108

