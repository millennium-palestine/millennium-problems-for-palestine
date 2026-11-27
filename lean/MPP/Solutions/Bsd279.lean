import Mathlib
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd278
import MPP.Solutions.Bsd243
import MPP.Solutions.Bsd275
import MPP.Solutions.Bsd276
import MPP.Solutions.Bsd312

namespace MPP.Solutions.Bsd279

open Polynomial

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic],
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → (5 : K) ≠ 0 →
      25 ≤ Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0} := by
  intro K _ _ _ W _ h2 h3 h5
  have hsq : Squarefree (W.preΨ' 5) := MPP.Solutions.Bsd278.main K W h5
  haveI hfin : Finite {P : W.toAffine.Point // (5 : ℤ) • P = 0} := MPP.Solutions.Bsd312.main K W h5
  have h5' : ((5 : ℕ) : K) ≠ 0 := by exact_mod_cast h5
  have hdeg : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' h5']
    norm_num
  have hp0 : W.preΨ' 5 ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  -- the twelve roots of preΨ' 5, all distinct
  have hcard : Multiset.card (W.preΨ' 5).roots = 12 := by
    rw [← hdeg]
    exact (splits_iff_card_roots.mp (IsAlgClosed.splits _))
  have hnd : (W.preΨ' 5).roots.Nodup := nodup_roots (PerfectField.separable_iff_squarefree.mpr hsq)
  set S : Finset K := (W.preΨ' 5).roots.toFinset with hS
  have hSc : S.card = 12 := by
    rw [hS, Multiset.toFinset_card_of_nodup hnd, hcard]
  have hroot : ∀ x, x ∈ S ↔ (W.preΨ' 5).eval x = 0 := by
    intro x
    rw [hS, Multiset.mem_toFinset, mem_roots hp0]
    rfl
  -- the 3-division polynomial does not vanish at a root of preΨ' 5 (bsd-276)
  have hΨne : ∀ x ∈ S, 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ ≠ 0 :=
    fun x hx h => MPP.Solutions.Bsd276.main K W x h2 h3 h5 h ((hroot x).mp hx)
  -- lifts of the roots to points (bsd-243)
  have hlift : ∀ x : K, ∃ y : K, W.toAffine.Nonsingular x y :=
    fun x => MPP.Solutions.Bsd243.main K W x h2
  choose yl hyl using hlift
  -- the lifted points are not 2-torsion: a vanishing ψ₂ would force ψ₃ = 0 at the root
  have hD : ∀ x ∈ S, 2 * yl x + W.a₁ * x + W.a₃ ≠ 0 := by
    intro x hx hD0
    have hev : (W.preΨ' 5).eval x = 0 := (hroot x).mp hx
    have hc := (WeierstrassCurve.Affine.equation_iff (W := W) x (yl x)).mp (hyl x).1
    have hg : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination (2 * yl x + W.a₁ * x + W.a₃) * hD0 - 4 * hc
    have hΨ2 : W.Ψ₂Sq.eval x = 0 := by
      unfold WeierstrassCurve.Ψ₂Sq
      simp
      linear_combination hg
    have hid : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
      have h := W.preΨ'_odd 0
      norm_num [W.preΨ'_four, W.preΨ'_two, W.preΨ'_one, W.preΨ'_three] at h
      linear_combination h
    rw [hid] at hev
    simp only [eval_sub, eval_mul, eval_pow, hΨ2] at hev
    have e : (W.Ψ₃.eval x) ^ 3 = 0 := by linear_combination -hev
    have h3x : W.Ψ₃.eval x = 0 := pow_eq_zero_iff (by norm_num) |>.mp e
    apply hΨne x hx
    simpa [WeierstrassCurve.Ψ₃] using h3x
  -- the five-torsion points over the roots (bsd-275)
  let Pt : K → W.toAffine.Point := fun x => WeierstrassCurve.Affine.Point.some x (yl x) (hyl x)
  have hP5 : ∀ x ∈ S, (5 : ℤ) • Pt x = 0 := fun x hx =>
    MPP.Solutions.Bsd275.main K W x (yl x) (hyl x) (hD x hx) (hΨne x hx) ((hroot x).mp hx)
  have hpt0 : ∀ x, Pt x ≠ 0 := fun x => WeierstrassCurve.Affine.Point.some_ne_zero (hyl x)
  -- a point of order dividing 5 is never equal to its negative unless it is zero
  have hne : ∀ P : W.toAffine.Point, (5 : ℤ) • P = 0 → P ≠ 0 → P ≠ -P := by
    intro P h5P hP0 hPP
    apply hP0
    have h2P : P + P = 0 := by
      calc P + P = -P + P := by rw [← hPP]
        _ = 0 := neg_add_cancel P
    have e5 : (5 : ℤ) • P = P + (P + P) + (P + P) := by
      rw [show (5 : ℤ) = 1 + 2 + 2 by norm_num, add_zsmul, add_zsmul, one_zsmul, two_zsmul]
    have hfive : P + (P + P) + (P + P) = 0 := by rw [← e5]; exact h5P
    rw [h2P, add_zero, add_zero] at hfive
    exact hfive
  -- equal x-coordinates force equal roots
  have hxeq : ∀ x y : K, (Pt x = Pt y ∨ Pt x = -Pt y) → x = y := by
    intro x y h
    rcases h with h | h
    · simp only [Pt, WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1
    · simp only [Pt, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1
  -- the 25 points: 0 and ±Pt x for the twelve roots x
  let F : Option (↥S × Bool) → {P : W.toAffine.Point // (5 : ℤ) • P = 0} := fun a =>
    match a with
    | none => ⟨0, smul_zero _⟩
    | some (x, true) => ⟨Pt x, hP5 x x.2⟩
    | some (x, false) => ⟨-Pt x, by rw [smul_neg, hP5 x x.2, neg_zero]⟩
  have hP5' : ∀ z : ↥S, (5 : ℤ) • Pt z = 0 := fun z => hP5 z z.2
  have hinj : Function.Injective F := by
    rintro (_ | ⟨x, _ | _⟩) (_ | ⟨y, _ | _⟩) hab
    all_goals have hv := congrArg Subtype.val hab
    all_goals simp only [F] at hv
    all_goals first
      | rfl
      | exact absurd hv (hpt0 _)
      | exact absurd hv.symm (hpt0 _)
      | exact absurd hv (neg_ne_zero.mpr (hpt0 _))
      | exact absurd hv.symm (neg_ne_zero.mpr (hpt0 _))
      | (have hxy := Subtype.ext (hxeq _ _ (Or.inl hv)); subst hxy; rfl)
      | (have hxy := Subtype.ext (hxeq _ _ (Or.inr hv)); subst hxy;
          exact absurd hv (hne _ (hP5' _) (hpt0 _)))
      | (have hxy := Subtype.ext (hxeq _ _ (Or.inr hv.symm)); subst hxy;
          exact absurd hv.symm (hne _ (hP5' _) (hpt0 _)))
      | (have hxy := Subtype.ext (hxeq _ _ (Or.inl (neg_inj.mp hv))); subst hxy; rfl)
  have h25 : Nat.card (Option (↥S × Bool)) = 25 := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, hSc]
  calc 25 = Nat.card (Option (↥S × Bool)) := h25.symm
    _ ≤ Nat.card {P : W.toAffine.Point // (5 : ℤ) • P = 0} := Nat.card_le_card_of_injective F hinj

end MPP.Solutions.Bsd279
