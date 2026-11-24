import Mathlib

namespace MPP.Solutions.Bsd091

theorem main : ∀ (K : Type) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
    S.Finite →
      Finite (IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K)
        (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))) (n := 2)) →
      Finite (IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K) (S := S) (n := 2)) := by
  intro K _ _ S hS h0
  classical
  set G := IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K) (K := K) (S := S) (n := 2)
    with hGdef
  let φ := IsDedekindDomain.selmerGroup.valuation (R := NumberField.RingOfIntegers K) (K := K) (S := S) (n := 2)
  haveI : Finite (S → Multiplicative (ZMod 2)) := by
    haveI := hS.to_subtype
    infer_instance
  have hran : Finite φ.range := Subtype.finite
  have hker : Finite φ.ker := by
    rw [IsDedekindDomain.selmerGroup.valuation_ker_eq]
    exact Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : ↥(IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers K)
      (K := K) (S := (∅ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))) (n := 2)))) (by
        intro a b hab
        have h2 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h2))
  have hquot : Finite (G ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm
  have hidx : φ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card G = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index φ.ker).symm
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact mul_ne_zero (Nat.card_pos (α := φ.ker)).ne' hidx

end MPP.Solutions.Bsd091
