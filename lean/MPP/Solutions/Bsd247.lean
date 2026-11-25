import Mathlib
import MPP.Solutions.Bsd216
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd246

namespace MPP.Solutions.Bsd247

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (5 : K) ≠ 0 → Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0} ≤ 25 := by
  intro K _ _ W _ h5
  classical
  have hm5 : ((5 : ℕ) : K) ≠ 0 := by exact_mod_cast h5
  have hdeg : (W.preΨ' 5).natDegree = 12 := by
    have h := W.natDegree_preΨ' hm5
    rw [if_neg (by decide)] at h
    rw [h]
    norm_num
  have hne : W.preΨ' 5 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hR : (W.preΨ' 5).roots.toFinset.card ≤ 12 := by
    have h := MPP.Solutions.Bsd216.main K W 5 (by decide) hm5
    exact h.trans (by norm_num)
  -- the points over one x-coordinate form a set of size at most 2
  have hfib : ∀ x : K, ∃ A : Finset W.toAffine.Point, A.card ≤ 2 ∧
      ∀ P : W.toAffine.Point, (∃ y : K, ∃ h : W.toAffine.Nonsingular x y,
        P = WeierstrassCurve.Affine.Point.some x y h) → P ∈ A := by
    intro x
    by_cases hne' : ∃ P : W.toAffine.Point, ∃ y : K, ∃ h : W.toAffine.Nonsingular x y,
        P = WeierstrassCurve.Affine.Point.some x y h
    · obtain ⟨P0, y0, h0, hP0⟩ := hne'
      refine ⟨{P0, -P0}, Finset.card_le_two, ?_⟩
      rintro P ⟨y, h, rfl⟩
      rcases MPP.Solutions.Bsd217.main K W x y y0 h h0 with h1 | h1
      · rw [← hP0] at h1
        simp [h1]
      · rw [← hP0] at h1
        simp [h1]
    · refine ⟨∅, by simp, ?_⟩
      rintro P ⟨y, h, rfl⟩
      exact (hne' ⟨_, y, h, rfl⟩).elim
  choose A hAcard hAmem using hfib
  -- every 5-torsion point lies in the finset {0} ∪ ⋃ over the roots of ψ₅
  have hsub : {P : W.toAffine.Point | (5 : ℤ) • P = 0} ⊆
      ↑(insert (0 : W.toAffine.Point) ((W.preΨ' 5).roots.toFinset.biUnion A)) := by
    rintro (_ | ⟨x, y, h⟩) hP
    · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
    · have hx : (W.preΨ' 5).eval x = 0 := MPP.Solutions.Bsd246.main K W x y h hP
      have hxR : x ∈ (W.preΨ' 5).roots.toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hx)
      exact Finset.mem_coe.mpr
        (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hxR, hAmem x _ ⟨y, h, rfl⟩⟩))
  have hT : (insert (0 : W.toAffine.Point) ((W.preΨ' 5).roots.toFinset.biUnion A)).card ≤ 25 := by
    calc (insert (0 : W.toAffine.Point) ((W.preΨ' 5).roots.toFinset.biUnion A)).card
        ≤ ((W.preΨ' 5).roots.toFinset.biUnion A).card + 1 := Finset.card_insert_le _ _
      _ ≤ ∑ x ∈ (W.preΨ' 5).roots.toFinset, (A x).card + 1 := by
          gcongr
          exact Finset.card_biUnion_le
      _ ≤ ∑ x ∈ (W.preΨ' 5).roots.toFinset, 2 + 1 := by
          gcongr with x
          exact hAcard x
      _ = (W.preΨ' 5).roots.toFinset.card * 2 + 1 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 25 := by omega
  calc Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0}
      = ({P : W.toAffine.Point | (5 : ℤ) • P = 0} : Set W.toAffine.Point).ncard :=
        (Nat.card_coe_set_eq _)
    _ ≤ (↑(insert (0 : W.toAffine.Point) ((W.preΨ' 5).roots.toFinset.biUnion A)) :
          Set W.toAffine.Point).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (insert (0 : W.toAffine.Point) ((W.preΨ' 5).roots.toFinset.biUnion A)).card :=
        Set.ncard_coe_finset _
    _ ≤ 25 := hT

end MPP.Solutions.Bsd247
