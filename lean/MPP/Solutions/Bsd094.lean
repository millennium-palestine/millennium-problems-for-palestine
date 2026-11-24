import Mathlib

namespace MPP.Solutions.Bsd094

open scoped nonZeroDivisors

-- units of a number field have finitely many square classes (the proof of bsd-090)
theorem units_sq : ∀ (K : Type) [Field K] [NumberField K],
    ∃ D : Finset (NumberField.RingOfIntegers K)ˣ,
      ∀ u : (NumberField.RingOfIntegers K)ˣ, ∃ d ∈ D, ∃ v : (NumberField.RingOfIntegers K)ˣ, u = d * v ^ 2 := by
  intro K _ _
  classical
  haveI : Group.FG (NumberField.RingOfIntegers K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  haveI : (powMonoidHom (α := (NumberField.RingOfIntegers K)ˣ) 2).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ (by norm_num)
  haveI : Fintype ((NumberField.RingOfIntegers K)ˣ ⧸ (powMonoidHom (α := (NumberField.RingOfIntegers K)ˣ) 2).range) :=
    Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : (NumberField.RingOfIntegers K)ˣ ⧸
    (powMonoidHom (α := (NumberField.RingOfIntegers K)ˣ) 2).range => q.out), ?_⟩
  intro u
  obtain ⟨⟨h, hh⟩, hout⟩ := QuotientGroup.mk_out_eq_mul
    (powMonoidHom (α := (NumberField.RingOfIntegers K)ˣ) 2).range u
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (Subgroup.inv_mem _ hh)
  have hw2 : w ^ 2 = h⁻¹ := hw
  refine ⟨(QuotientGroup.mk u : (NumberField.RingOfIntegers K)ˣ ⧸
    (powMonoidHom (α := (NumberField.RingOfIntegers K)ˣ) 2).range).out,
    Finset.mem_image.mpr ⟨QuotientGroup.mk u, Finset.mem_univ _, rfl⟩, w, ?_⟩
  rw [hw2, hout]
  simp

-- an element with even valuations has principal ideal a square of a fractional ideal (the proof of bsd-093)
theorem even_sq_ideal : ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n)) →
    ∃ J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K,
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x = J ^ 2 := by
  intro K _ _ x hx hev
  classical
  have hI0 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hx
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

-- the square root of a principal ideal with even valuations, with its integral part
theorem ideal_form (K : Type) [Field K] [NumberField K] (x : K) (hx : x ≠ 0)
    (J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
    (hJ : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x = J ^ 2) :
    ∃ (A : K) (I : Ideal (NumberField.RingOfIntegers K)), A ≠ 0 ∧ I ≠ 0 ∧
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
          ((I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ^ 2 := by
  obtain ⟨a, I, ha, hJI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  refine ⟨(algebraMap (NumberField.RingOfIntegers K) K a)⁻¹, I,
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr ha), ?_, ?_⟩
  · intro h0
    have hJ0 : J = 0 := by rw [hJI, h0]; simp
    have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x = 0 := by
      rw [hJ, hJ0]; simp
    exact (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) h1
  · rw [hJ, hJI, mul_pow, FractionalIdeal.spanSingleton_pow]

-- two even elements in the same ideal class differ by a square times a unit
theorem same_class (K : Type) [Field K] [NumberField K] (x x' : K)
    (A A' : K) (I I' : Ideal (NumberField.RingOfIntegers K)) (hA : A ≠ 0) (hA' : A' ≠ 0)
    (hI : I ≠ 0) (hI' : I' ≠ 0)
    (hxI : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
          ((I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ^ 2)
    (hxI' : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x' =
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A' ^ 2) *
          ((I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ^ 2)
    (hcls : ClassGroup.mk0 (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (NumberField.RingOfIntegers K))⁰) =
      ClassGroup.mk0 ⟨I', mem_nonZeroDivisors_of_ne_zero hI'⟩) :
    ∃ (β : K) (z : (NumberField.RingOfIntegers K)ˣ),
      x = β ^ 2 * x' * algebraMap (NumberField.RingOfIntegers K) K z := by
  obtain ⟨r, s, hr, hs, hrs⟩ := ClassGroup.mk0_eq_mk0_iff.mp hcls
  have hP : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (algebraMap (NumberField.RingOfIntegers K) K r) * (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (algebraMap (NumberField.RingOfIntegers K) K s) * (I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) := by
    have h := congrArg (fun J : Ideal (NumberField.RingOfIntegers K) =>
      (J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) hrs
    simpa only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] using h
  have hsq : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (algebraMap (NumberField.RingOfIntegers K) K r ^ 2) *
          (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2 =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (algebraMap (NumberField.RingOfIntegers K) K s ^ 2) *
          (I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2 := by
    have h := congrArg (· ^ 2) hP
    simpa only [mul_pow, FractionalIdeal.spanSingleton_pow] using h
  have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((A * algebraMap (NumberField.RingOfIntegers K) K s / A') ^ 2 * x') =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (A ^ 2 * algebraMap (NumberField.RingOfIntegers K) K s ^ 2) *
          (I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2 := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, hxI', ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    have hk : (A * algebraMap (NumberField.RingOfIntegers K) K s / A') ^ 2 * A' ^ 2 =
        A ^ 2 * algebraMap (NumberField.RingOfIntegers K) K s ^ 2 := by
      field_simp
    rw [hk]
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        (algebraMap (NumberField.RingOfIntegers K) K r ^ 2 * x) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
        ((A * algebraMap (NumberField.RingOfIntegers K) K s / A') ^ 2 * x') := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (algebraMap (NumberField.RingOfIntegers K) K r ^ 2 * x)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (algebraMap (NumberField.RingOfIntegers K) K r ^ 2) *
          FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x :=
            (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (algebraMap (NumberField.RingOfIntegers K) K r ^ 2) *
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
            (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2) := by
            rw [hxI]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (algebraMap (NumberField.RingOfIntegers K) K r ^ 2) *
            (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2) := by
            rw [mul_left_comm]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (algebraMap (NumberField.RingOfIntegers K) K s ^ 2) *
            (I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2) := by
            rw [hsq]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            (A ^ 2 * algebraMap (NumberField.RingOfIntegers K) K s ^ 2) *
          (I' : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) ^ 2 := by
            rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
            ((A * algebraMap (NumberField.RingOfIntegers K) K s / A') ^ 2 * x') := e1.symm
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp h1.symm
  refine ⟨A * algebraMap (NumberField.RingOfIntegers K) K s / (A' * algebraMap (NumberField.RingOfIntegers K) K r), z, ?_⟩
  have hr' : algebraMap (NumberField.RingOfIntegers K) K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hr
  simp only [Units.smul_def, Algebra.smul_def] at hz
  have hα2 : algebraMap (NumberField.RingOfIntegers K) K r ^ 2 ≠ 0 := pow_ne_zero 2 hr'
  apply mul_left_cancel₀ hα2
  rw [← hz]
  field_simp

theorem main : ∀ (K : Type) [Field K] [NumberField K],
    ∃ D : Finset K, ∀ x : K, x ≠ 0 →
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n)) →
      ∃ d ∈ D, ∃ w : K, x = d * w ^ 2 := by
  intro K _ _
  classical
  obtain ⟨DU, hDU⟩ := units_sq K
  have hform : ∀ x : K, (x ≠ 0 ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n)) →
      ∃ (A : K) (I : Ideal (NumberField.RingOfIntegers K)), A ≠ 0 ∧ I ≠ 0 ∧
        FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) x =
          FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (A ^ 2) *
            ((I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ^ 2 := by
    rintro x ⟨hx, hev⟩
    obtain ⟨J, hJ⟩ := even_sq_ideal K x hx hev
    exact ideal_form K x hx J hJ
  choose! A I hA hI hEq using hform
  -- the ideal class of an element with even valuations (a junk value otherwise)
  let g : K → ClassGroup (NumberField.RingOfIntegers K) := fun x =>
    if h : x ≠ 0 ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n) then
      ClassGroup.mk0 ⟨I x, mem_nonZeroDivisors_of_ne_zero (hI x h)⟩
    else 1
  -- one chosen element for each class that occurs
  let rep : ClassGroup (NumberField.RingOfIntegers K) → K := fun c =>
    if h : ∃ y : K, (y ≠ 0 ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        ∃ n : ℤ, v.valuation K y = WithZero.exp (2 * n)) ∧ g y = c then
      Classical.choose h
    else 0
  refine ⟨((Finset.univ : Finset (ClassGroup (NumberField.RingOfIntegers K))) ×ˢ DU).image
    (fun p => rep p.1 * algebraMap (NumberField.RingOfIntegers K) K p.2), ?_⟩
  intro x hx hev
  have hPx : x ≠ 0 ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n) := ⟨hx, hev⟩
  have hex : ∃ y : K, (y ≠ 0 ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ n : ℤ, v.valuation K y = WithZero.exp (2 * n)) ∧ g y = g x := ⟨x, hPx, rfl⟩
  have hrepx : rep (g x) = Classical.choose hex := dif_pos hex
  have hx0 := Classical.choose_spec hex
  set x0 := Classical.choose hex with hx0def
  have hx0P := hx0.1
  have hgx0 : g x0 = g x := hx0.2
  have hcls : ClassGroup.mk0 ⟨I x, mem_nonZeroDivisors_of_ne_zero (hI x hPx)⟩ =
      ClassGroup.mk0 ⟨I x0, mem_nonZeroDivisors_of_ne_zero (hI x0 hx0P)⟩ := by
    have h1 : g x = ClassGroup.mk0 ⟨I x, mem_nonZeroDivisors_of_ne_zero (hI x hPx)⟩ := by
      simp only [g, dif_pos hPx]
    have h2 : g x0 = ClassGroup.mk0 ⟨I x0, mem_nonZeroDivisors_of_ne_zero (hI x0 hx0P)⟩ := by
      simp only [g, dif_pos hx0P]
    rw [← h1, ← h2, hgx0]
  obtain ⟨β, z, hβ⟩ := same_class K x x0 (A x) (A x0) (I x) (I x0) (hA x hPx) (hA x0 hx0P)
    (hI x hPx) (hI x0 hx0P) (hEq x hPx) (hEq x0 hx0P) hcls
  obtain ⟨d, hd, v, hz⟩ := hDU z
  have hzK : algebraMap (NumberField.RingOfIntegers K) K (z : NumberField.RingOfIntegers K) =
      algebraMap (NumberField.RingOfIntegers K) K (d : NumberField.RingOfIntegers K) *
        algebraMap (NumberField.RingOfIntegers K) K (v : NumberField.RingOfIntegers K) ^ 2 := by
    have h := congrArg (fun u : (NumberField.RingOfIntegers K)ˣ => (u : NumberField.RingOfIntegers K)) hz
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
    rw [h, map_mul, map_pow]
  refine ⟨x0 * algebraMap (NumberField.RingOfIntegers K) K d,
    Finset.mem_image.mpr ⟨(g x, d), Finset.mem_product.mpr ⟨Finset.mem_univ _, hd⟩, by simp only [hrepx]⟩,
    β * algebraMap (NumberField.RingOfIntegers K) K v, ?_⟩
  rw [hβ, hzK]
  ring

end MPP.Solutions.Bsd094
