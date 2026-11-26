import Mathlib

namespace MPP.Solutions.Bsd277

open Polynomial

theorem root_mem_range (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p))
    (hx : x ^ p = x) : ∃ x0 : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) x0 = x := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfp : ∀ b : ZMod p, (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) b) ^ p =
      algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) b := fun b => by
    rw [← map_pow, ZMod.pow_card]
  have hZcard : (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective,
      Finset.card_univ, ZMod.card]
  by_cases hxZ : x ∈ Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
  · obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hxZ
    exact ⟨b, hb⟩
  · exfalso
    have hScard : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).card
        = p + 1 := by
      rw [Finset.card_insert_of_notMem hxZ, hZcard]
    have hQne : (X ^ p - X : (AlgebraicClosure (ZMod p))[X]) ≠ 0 := by
      intro h0
      have hc := congrArg (fun q : (AlgebraicClosure (ZMod p))[X] => q.coeff p) h0
      have hne2 : (1 : ℕ) ≠ p := by omega
      simp [coeff_X, coeff_X_pow, hne2] at hc
    have hsub : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).val ⊆
        (X ^ p - X : (AlgebraicClosure (ZMod p))[X]).roots := by
      intro a ha
      rw [Finset.mem_val, Finset.mem_insert] at ha
      rw [mem_roots hQne]
      rcases ha with ha | ha
      · rw [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero, ha]
        exact hx
      · obtain ⟨b, -, hb⟩ := Finset.mem_image.mp ha
        rw [IsRoot.def, eval_sub, eval_pow, eval_X, sub_eq_zero, ← hb]
        exact hfp b
    have hle := card_le_degree_of_subset_roots hsub
    have hdeg : (X ^ p - X : (AlgebraicClosure (ZMod p))[X]).natDegree ≤ p := by
      refine (natDegree_sub_le _ _).trans ?_
      rw [natDegree_X_pow, natDegree_X]
      omega
    have hfin := hle.trans hdeg
    rw [hScard] at hfin
    omega

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))]
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} =
      Nat.card W.toAffine.Point := by
  intro p _ _ W _
  have hfrob : ∀ z : AlgebraicClosure (ZMod p),
      FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) z = z ^ p := fun z => by
    rw [FiniteField.frobeniusAlgHom_apply, ZMod.card]
  have hfix : ∀ P : (W.baseChange (ZMod p)).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
        (WeierstrassCurve.Affine.Point.map (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) P) =
        WeierstrassCurve.Affine.Point.map (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) P := by
    intro P
    rw [WeierstrassCurve.Affine.Point.map_map,
      Subsingleton.elim ((FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))).comp
        (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))]
  let g : W.toAffine.Point →
      {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
        WeierstrassCurve.Affine.Point.map (W' := W)
          (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} :=
    fun P => ⟨WeierstrassCurve.Affine.Point.map (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) P, hfix P⟩
  have hg : Function.Bijective g := by
    constructor
    · intro P Q h
      exact WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
        (congrArg Subtype.val h)
    · rintro ⟨Q, hQ⟩
      cases Q with
      | zero =>
        exact ⟨0, Subtype.ext (WeierstrassCurve.Affine.Point.map_zero _)⟩
      | some x y h =>
        rw [WeierstrassCurve.Affine.Point.map_some] at hQ
        simp only [WeierstrassCurve.Affine.Point.some.injEq] at hQ
        obtain ⟨hx, hy⟩ := hQ
        rw [hfrob] at hx hy
        obtain ⟨x0, hx0⟩ := root_mem_range p x hx
        obtain ⟨y0, hy0⟩ := root_mem_range p y hy
        have h0 : (W.baseChange (ZMod p)).toAffine.Nonsingular x0 y0 :=
          (WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
            (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))).injective x0 y0).mp (by
            rw [show (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) x0 = x from hx0,
              show (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) y0 = y from hy0]
            exact h)
        refine ⟨WeierstrassCurve.Affine.Point.some x0 y0 h0, Subtype.ext ?_⟩
        show WeierstrassCurve.Affine.Point.map (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
          (WeierstrassCurve.Affine.Point.some x0 y0 h0) = _
        rw [WeierstrassCurve.Affine.Point.map_some]
        subst hx0 hy0
        rfl
  exact (Nat.card_eq_of_bijective g hg).symm

end MPP.Solutions.Bsd277
