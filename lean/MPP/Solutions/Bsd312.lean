import Mathlib
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd246

namespace MPP.Solutions.Bsd312

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (5 : K) ≠ 0 → Finite {P : W.toAffine.Point // (5 : ℤ) • P = 0} := by
  intro K _ _ W _ h5
  classical
  -- the 5-division polynomial is nonzero of degree 12, so it has finitely many roots
  have hdeg : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' (n := 5) (by exact_mod_cast h5)]
    norm_num [Nat.even_iff]
  have hf0 : W.preΨ' 5 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hRts : {x : K | (W.preΨ' 5).eval x = 0}.Finite := Polynomial.finite_setOf_isRoot hf0
  -- the affine points over a fixed x-coordinate: at most two, by bsd-217
  let T : K → Set W.toAffine.Point := fun x => {P | ∃ (y : K) (h : W.toAffine.Nonsingular x y),
    P = WeierstrassCurve.Affine.Point.some x y h}
  have hT : ∀ x, (T x).Finite := by
    intro x
    by_cases hne : (T x).Nonempty
    · obtain ⟨Q, y0, h0, rfl⟩ := hne
      apply Set.Finite.subset (Set.toFinite
        ({WeierstrassCurve.Affine.Point.some x y0 h0, -WeierstrassCurve.Affine.Point.some x y0 h0} :
          Set W.toAffine.Point))
      rintro P ⟨y, h, rfl⟩
      rcases MPP.Solutions.Bsd217.main K W x y y0 h h0 with hs | hs
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl hs
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr hs
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  -- every five-torsion point is zero or lies over a root of preΨ′ 5 (bsd-246)
  have hsub : {P : W.toAffine.Point | (5 : ℤ) • P = 0} ⊆
      insert 0 (⋃ x ∈ {x : K | (W.preΨ' 5).eval x = 0}, T x) := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact Set.mem_insert _ _
    · apply Set.mem_insert_of_mem
      have hx : (W.preΨ' 5).eval x = 0 := MPP.Solutions.Bsd246.main K W x y h hP
      exact Set.mem_biUnion hx ⟨y, h, rfl⟩
  have hfin : (insert (0 : W.toAffine.Point) (⋃ x ∈ {x : K | (W.preΨ' 5).eval x = 0}, T x)).Finite :=
    (hRts.biUnion fun x _ => hT x).insert 0
  exact Set.finite_coe_iff.mpr (hfin.subset hsub)

end MPP.Solutions.Bsd312
