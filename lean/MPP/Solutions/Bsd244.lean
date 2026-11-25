import Mathlib
import MPP.Solutions.Bsd205
import MPP.Solutions.Bsd217
import MPP.Solutions.Bsd240
import MPP.Solutions.Bsd241
import MPP.Solutions.Bsd242
import MPP.Solutions.Bsd243

namespace MPP.Solutions.Bsd244

open Polynomial

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    (2 : K) ≠ 0 → (3 : K) ≠ 0 → 9 ≤ Nat.card {P : W.toAffine.Point // (3 : ℤ) • P = 0} := by
  intro K _ _ _ W _ h2 h3
  have h4 : (4 : K) ≠ 0 := by
    have e : (4 : K) = 2 * 2 := by norm_num
    rw [e]
    exact mul_ne_zero h2 h2
  have hb8 : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := W.b_relation
  -- the discriminant form Q = -4Δ is nonzero, since Δ is a unit
  have hQ : W.b₂ ^ 3 * W.b₆ - W.b₂ ^ 2 * W.b₄ ^ 2 - 36 * W.b₂ * W.b₄ * W.b₆ + 32 * W.b₄ ^ 3
      + 108 * W.b₆ ^ 2 ≠ 0 := by
    intro hq
    have hΔ : (4 : K) * W.Δ = 0 := by
      unfold WeierstrassCurve.Δ
      linear_combination (-W.b₂ ^ 2) * hb8 - hq
    exact W.isUnit_Δ.ne_zero ((mul_eq_zero.mp hΔ).resolve_left h4)
  -- the roots of 4ψ₃ (bsd-242) and their root form
  obtain ⟨f, hfinj, hfroot⟩ := MPP.Solutions.Bsd242.main K W.b₂ W.b₄ W.b₆ h2 h3 hQ
  have hΨ : ∀ i, 3 * f i ^ 4 + W.b₂ * f i ^ 3 + 3 * W.b₄ * f i ^ 2 + 3 * W.b₆ * f i + W.b₈ = 0 := by
    intro i
    have h := mul_eq_zero.mp (show (4 : K) * (3 * f i ^ 4 + W.b₂ * f i ^ 3 + 3 * W.b₄ * f i ^ 2
        + 3 * W.b₆ * f i + W.b₈) = 0 by linear_combination hfroot i + hb8)
    exact h.resolve_left h4
  have hP4 : ∀ a : K, 3 * a ^ 4 + W.b₂ * a ^ 3 + 3 * W.b₄ * a ^ 2 + 3 * W.b₆ * a + W.b₈ = 0 →
      12 * a ^ 4 + 4 * W.b₂ * a ^ 3 + 12 * W.b₄ * a ^ 2 + 12 * W.b₆ * a + (W.b₂ * W.b₆ - W.b₄ ^ 2) = 0 := by
    intro a ha
    linear_combination 4 * ha - hb8
  -- lifts of the roots to points (bsd-243)
  have hlift : ∀ i, ∃ y : K, W.toAffine.Nonsingular (f i) y :=
    fun i => MPP.Solutions.Bsd243.main K W (f i) h2
  choose yl hyl using hlift
  let Pt : Fin 4 → W.toAffine.Point := fun i => WeierstrassCurve.Affine.Point.some (f i) (yl i) (hyl i)
  -- the lifted points are not 2-torsion (bsd-241)
  have hD : ∀ i, 2 * yl i + W.a₁ * f i + W.a₃ ≠ 0 := by
    intro i hD0
    have hc := (WeierstrassCurve.Affine.equation_iff (W := W) (f i) (yl i)).mp (hyl i).1
    have hg : 4 * f i ^ 3 + W.b₂ * f i ^ 2 + 2 * W.b₄ * f i + W.b₆ = 0 := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination (2 * yl i + W.a₁ * f i + W.a₃) * hD0 - 4 * hc
    exact hQ (MPP.Solutions.Bsd241.main K W.b₂ W.b₄ W.b₆ (f i) (hfroot i) hg)
  -- the lifted points are 3-torsion (bsd-240)
  have hPt3 : ∀ i, (3 : ℤ) • Pt i = 0 := fun i =>
    MPP.Solutions.Bsd240.main K W (f i) (yl i) (hyl i) (hD i) (hΨ i)
  have hpt0 : ∀ i, Pt i ≠ 0 := fun i => WeierstrassCurve.Affine.Point.some_ne_zero (hyl i)
  -- a 3-torsion point is never equal to its negative unless it is zero
  have hne : ∀ P : W.toAffine.Point, (3 : ℤ) • P = 0 → P ≠ 0 → P ≠ -P := by
    intro P h3P hP0 hPP
    apply hP0
    have h2P : P + P = 0 := by
      have := congrArg (fun Q => P + Q) hPP
      simpa using this
    have e3 : (3 : ℤ) • P = P + (P + P) := by
      rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, one_zsmul, two_zsmul]
    rw [e3, h2P, add_zero] at h3P
    exact h3P
  have hpp : ∀ i, Pt i ≠ -Pt i := fun i => hne _ (hPt3 i) (hpt0 i)
  -- equal x-coordinates force equal indices
  have hxeq : ∀ i j, Pt i = Pt j ∨ Pt i = -Pt j → i = j := by
    intro i j h
    apply hfinj
    rcases h with h | h
    · simp only [Pt, WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1
    · simp only [Pt, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h
      exact h.1
  -- the nine candidate points: 0, ±Pt i
  let F : Option (Fin 4 × Bool) → {P : W.toAffine.Point // (3 : ℤ) • P = 0} := fun a =>
    match a with
    | none => ⟨0, smul_zero _⟩
    | some (i, true) => ⟨Pt i, hPt3 i⟩
    | some (i, false) => ⟨-Pt i, by rw [smul_neg, hPt3 i, neg_zero]⟩
  have hinj : Function.Injective F := by
    rintro (_ | ⟨i, _ | _⟩) (_ | ⟨j, _ | _⟩) hab <;>
      have hv := congrArg Subtype.val hab <;> simp only [F] at hv <;>
      first
      | rfl
      | exact absurd hv (hpt0 _)
      | exact absurd hv.symm (hpt0 _)
      | exact absurd hv (neg_ne_zero.mpr (hpt0 _))
      | exact absurd hv.symm (neg_ne_zero.mpr (hpt0 _))
      | (have hij := hxeq _ _ (Or.inl hv); subst hij; rfl)
      | (have hij := hxeq _ _ (Or.inr hv); subst hij; exact absurd hv (hpp _))
      | (have hij := hxeq _ _ (Or.inr hv.symm); subst hij; exact absurd hv.symm (hpp _))
      | (have hij := hxeq _ _ (Or.inl (neg_inj.mp hv)); subst hij; rfl)
  -- every x-coordinate of a 3-torsion point is a root of the 3-division polynomial, hence some f i
  have hroot : ∀ x : K, 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0 →
      ∃ i, f i = x := by
    intro x hx
    have h12 : (12 : K) ≠ 0 := by
      have e : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [e]
      exact mul_ne_zero (mul_ne_zero h2 h2) h3
    set Pp : K[X] := 12 * X ^ 4 + 4 * C W.b₂ * X ^ 3 + 12 * C W.b₄ * X ^ 2 + 12 * C W.b₆ * X
      + C (W.b₂ * W.b₆ - W.b₄ ^ 2) with hPp
    have hdeg : Pp.natDegree = 4 := by
      rw [hPp]
      compute_degree!
    have hPp0 : Pp ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hdeg
      omega
    have hmem : ∀ a : K, 12 * a ^ 4 + 4 * W.b₂ * a ^ 3 + 12 * W.b₄ * a ^ 2 + 12 * W.b₆ * a
        + (W.b₂ * W.b₆ - W.b₄ ^ 2) = 0 → a ∈ Pp.roots := by
      intro a ha
      rw [mem_roots hPp0, IsRoot.def, hPp]
      simp
      linear_combination ha
    have hS : (Finset.univ.image f).card = 4 := by
      rw [Finset.card_image_of_injective _ hfinj]
      simp
    by_contra hno
    have hxS : x ∉ Finset.univ.image f := by
      intro hm
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      exact hno ⟨i, hi⟩
    have hsub : (insert x (Finset.univ.image f)).val ⊆ Pp.roots := by
      intro a ha
      rw [Finset.mem_val, Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · exact hmem _ (hP4 _ hx)
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        exact hmem _ (hfroot i)
    have hle := card_le_degree_of_subset_roots hsub
    rw [Finset.card_insert_of_notMem hxS, hS, hdeg] at hle
    omega
  -- surjectivity: every 3-torsion point is one of the nine
  have hsurj : Function.Surjective F := by
    rintro ⟨P, hP3⟩
    cases P with
    | zero => exact ⟨none, Subtype.ext rfl⟩
    | @some x y h =>
      have hD0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
        intro hD0
        have hsame : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
            -WeierstrassCurve.Affine.Point.some x y h := by
          rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
          refine ⟨rfl, ?_⟩
          rw [WeierstrassCurve.Affine.negY]
          linear_combination hD0
        exact hne _ hP3 (WeierstrassCurve.Affine.Point.some_ne_zero h) hsame
      have hΨx : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0 := by
        obtain ⟨x₃, y₃, h₃, hdbl, hx₃⟩ := MPP.Solutions.Bsd205.main K W x y h hD0
        have e3 : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
            WeierstrassCurve.Affine.Point.some x y h + (WeierstrassCurve.Affine.Point.some x y h
              + WeierstrassCurve.Affine.Point.some x y h) := by
          rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, one_zsmul, two_zsmul]
        have h2P : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
            + WeierstrassCurve.Affine.Point.some x y h = -WeierstrassCurve.Affine.Point.some x y h := by
          rw [e3] at hP3
          rw [add_comm] at hP3
          exact eq_neg_of_add_eq_zero_left hP3
        rw [hdbl, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at h2P
        rw [h2P.1] at hx₃
        linear_combination hx₃
      obtain ⟨i, rfl⟩ := hroot x hΨx
      rcases MPP.Solutions.Bsd217.main K W (f i) y (yl i) h (hyl i) with hA | hB
      · exact ⟨some (i, true), Subtype.ext hA.symm⟩
      · exact ⟨some (i, false), Subtype.ext hB.symm⟩
  haveI : Finite {P : W.toAffine.Point // (3 : ℤ) • P = 0} := Finite.of_surjective F hsurj
  have h9 : Nat.card (Option (Fin 4 × Bool)) = 9 := by
    rw [Nat.card_eq_fintype_card]
    simp
  calc 9 = Nat.card (Option (Fin 4 × Bool)) := h9.symm
    _ ≤ Nat.card {P : W.toAffine.Point // (3 : ℤ) • P = 0} := Nat.card_le_card_of_injective F hinj

end MPP.Solutions.Bsd244
