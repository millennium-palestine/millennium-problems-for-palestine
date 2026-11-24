import Mathlib

namespace MPP.Solutions.Bsd090

theorem main : ∀ (K : Type) [Field K] [NumberField K],
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

end MPP.Solutions.Bsd090
