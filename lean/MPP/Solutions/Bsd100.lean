import Mathlib
import MPP.Solutions.Bsd091
import MPP.Solutions.Bsd092

namespace MPP.Solutions.Bsd100

-- even valuations give a trivial class modulo squares at v (the converse of even_of_mod)
theorem mod_of_even (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (X : Kˣ)
    (h : ∃ n : ℤ, v.valuation K (X : K) = WithZero.exp (2 * n)) :
    v.valuationOfNeZeroMod 2 (QuotientGroup.mk X) = 1 := by
  obtain ⟨n, hn⟩ := h
  have hval : ((v.valuationOfNeZero X : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (2 * n) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq, hn]
  have ha : v.valuationOfNeZero X = Multiplicative.ofAdd (2 * n) := WithZero.coe_inj.mp hval
  have key : Int.quotientZMultiplesNatEquivZMod 2
      (QuotientAddGroup.mk (Multiplicative.toAdd (v.valuationOfNeZero X))) = 0 := by
    rw [ha]
    change Int.quotientZMultiplesNatEquivZMod 2 (QuotientAddGroup.mk (2 * n)) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr ⟨n, by norm_num [mul_comm]⟩
  erw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply, ← QuotientGroup.coe_mk',
    QuotientGroup.map_mk']
  exact key

theorem main : ∀ (K : Type) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
    S.Finite → ∃ D : Finset K, ∀ x : K, x ≠ 0 →
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), v ∉ S →
        ∃ n : ℤ, v.valuation K x = WithZero.exp (2 * n)) →
      ∃ d ∈ D, ∃ w : K, x = d * w ^ 2 := by
  intro K _ _ S hS
  classical
  have hfin := MPP.Solutions.Bsd091.main K S hS (MPP.Solutions.Bsd092.main K)
  haveI := Fintype.ofFinite (IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K)
    (S := S) (n := 2))
  refine ⟨Finset.univ.image (fun g : IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K)
    (S := S) (n := 2) => ((g : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range).out : K)), ?_⟩
  intro x hx0 hev
  let X : Kˣ := Units.mk0 x hx0
  have hmem : (QuotientGroup.mk X : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range) ∈
      IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K) (S := S) (n := 2) :=
    fun v hv => mod_of_even K v X (hev v hv)
  let g : IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K) (S := S) (n := 2) :=
    ⟨QuotientGroup.mk X, hmem⟩
  have hout : QuotientGroup.mk ((g : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range).out) =
      (g : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range) := QuotientGroup.out_eq' _
  have hrel := QuotientGroup.eq.mp (hout.trans rfl)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hrel
  refine ⟨((g : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range).out : K),
    Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩, (y : K), ?_⟩
  have hyK := congrArg Units.val hy
  rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val] at hyK
  have hXK : ((X : Kˣ) : K) = x := Units.val_mk0 hx0
  have hr0 : ((((g : Kˣ ⧸ (powMonoidHom (2 : ℕ) : Kˣ →* Kˣ).range).out : Kˣ) : K)) ≠ 0 :=
    Units.ne_zero _
  rw [hyK, hXK]
  field_simp

end MPP.Solutions.Bsd100
