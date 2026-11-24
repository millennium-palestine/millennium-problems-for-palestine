import Mathlib
import MPP.Solutions.Bsd094

namespace MPP.Solutions.Bsd092

-- a class of K^× modulo squares whose 2-valuations are trivial has even valuations at every prime
theorem even_of_mod (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (X : Kˣ)
    (h : v.valuationOfNeZeroMod 2 (QuotientGroup.mk X) = 1) :
    ∃ n : ℤ, v.valuation K (X : K) = WithZero.exp (2 * n) := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply, ← QuotientGroup.coe_mk',
    QuotientGroup.map_mk'] at h
  have h3 : Int.quotientZMultiplesNatEquivZMod 2
      (QuotientAddGroup.mk (Multiplicative.toAdd (v.valuationOfNeZero X))) = 0 := h
  have h4 : ((Multiplicative.toAdd (v.valuationOfNeZero X) : ℤ) : ZMod 2) = 0 := h3
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h4
  have hm : Multiplicative.toAdd (v.valuationOfNeZero X) = 2 * k := by
    exact_mod_cast hk
  refine ⟨k, ?_⟩
  rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq, ← hm]
  rfl

-- the Selmer group K⟮∅, 2⟯ is finite, using the finite set of representatives of bsd-094
theorem main : ∀ (K : Type) [Field K] [NumberField K],
    Finite (IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))) (n := 2)) := by
  intro K _ _
  classical
  obtain ⟨D, hD⟩ := MPP.Solutions.Bsd094.main K
  let F : K → Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range := fun d =>
    if h : d = 0 then 1 else QuotientGroup.mk (Units.mk0 d h)
  have hsub : ((IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K)
      (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))) (n := 2) :
        Subgroup _) : Set (Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range)) ⊆ F '' (D : Set K) := by
    intro g hg
    obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨d, hd, w, hw⟩ := hD (X : K) (Units.ne_zero X)
      (fun v => even_of_mod K v X (hg v (Set.notMem_empty v)))
    have hd0 : d ≠ 0 := by
      rintro rfl
      apply Units.ne_zero X
      rw [hw]
      simp
    have hw0 : w ≠ 0 := by
      rintro rfl
      apply Units.ne_zero X
      rw [hw]
      simp
    refine ⟨d, hd, ?_⟩
    simp only [F, dif_neg hd0]
    apply QuotientGroup.eq.mpr
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp [hw, hd0]
  have hfin : (F '' (D : Set K)).Finite := (D.finite_toSet).image F
  exact (hfin.subset hsub).to_subtype

end MPP.Solutions.Bsd092
