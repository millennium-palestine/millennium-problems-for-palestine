import Mathlib

namespace MPP.Solutions.Bsd122

open Polynomial

theorem fixed_iff_prime (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p)) :
    x ^ p = x ↔ ∃ a : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a = x := by
  classical
  constructor
  · intro hx
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hq0 : (X ^ p - X : (AlgebraicClosure (ZMod p))[X]) ≠ 0 := by
      intro h
      have := congrArg (fun r : (AlgebraicClosure (ZMod p))[X] => r.coeff 1) h
      simp [coeff_X_pow, coeff_X, show (1 : ℕ) ≠ p by omega] at this
    have hdeg : (X ^ p - X : (AlgebraicClosure (ZMod p))[X]).natDegree ≤ p :=
      (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow p).le (natDegree_X_le.trans hp1.le))
    by_contra hnot
    have hnot' : x ∉ Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
      intro hmem
      apply hnot
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
      exact ⟨a, ha⟩
    have hcard : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).card = p + 1 := by
      rw [Finset.card_insert_of_notMem hnot', Finset.card_image_of_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective,
        Finset.card_univ, ZMod.card]
    have hsub : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).val ⊆
        (X ^ p - X : (AlgebraicClosure (ZMod p))[X]).roots := by
      intro z hz
      rw [Finset.mem_val, Finset.mem_insert, Finset.mem_image] at hz
      rw [mem_roots hq0]
      rcases hz with hz | ⟨a, _, ha⟩
      · rw [hz]
        simp only [IsRoot, eval_sub, eval_pow, eval_X]
        rw [hx, sub_self]
      · rw [← ha]
        simp only [IsRoot, eval_sub, eval_pow, eval_X]
        rw [← map_pow, ZMod.pow_card, sub_self]
    have := card_le_degree_of_subset_roots hsub
    omega
  · rintro ⟨a, rfl⟩
    rw [← map_pow, ZMod.pow_card]

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} =
      Nat.card W.toAffine.Point := by
  intro p _ _ W _
  -- the base change of W from ZMod p to itself is W
  have hWid : W.baseChange (ZMod p) = W := by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_id]
  -- the base change of points from F_p into the algebraic closure
  let g := WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
  have hg : Function.Injective g := WeierstrassCurve.Affine.Point.map_injective _
  have hfix : ∀ P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P ↔ P ∈ Set.range g := by
    have hcomp : (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))).comp
        (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) = Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)) :=
      Subsingleton.elim _ _
    intro P
    constructor
    · intro hP
      cases P with
      | zero => exact ⟨0, WeierstrassCurve.Affine.Point.map_zero _⟩
      | some x y h =>
        rw [WeierstrassCurve.Affine.Point.map_some] at hP
        obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hP
        have h1' : x ^ p = x := by simpa [ZMod.card] using h1
        have h2' : y ^ p = y := by simpa [ZMod.card] using h2
        obtain ⟨a, rfl⟩ := (fixed_iff_prime p x).mp h1'
        obtain ⟨b, rfl⟩ := (fixed_iff_prime p y).mp h2'
        have hn : (W.baseChange (ZMod p)).toAffine.Nonsingular a b :=
          (WeierstrassCurve.Affine.baseChange_nonsingular W
            (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))).toRingHom.injective a b).mp h
        exact ⟨WeierstrassCurve.Affine.Point.some a b hn, WeierstrassCurve.Affine.Point.map_some _ hn⟩
    · rintro ⟨Q, rfl⟩
      rw [WeierstrassCurve.Affine.Point.map_map, hcomp]
  calc Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P}
      = Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // P ∈ Set.range g} :=
        Nat.card_congr (Equiv.subtypeEquivRight hfix)
    _ = Nat.card (Set.range g) := rfl
    _ = Nat.card (W.baseChange (ZMod p)).toAffine.Point := Nat.card_range_of_injective hg
    _ = Nat.card W.toAffine.Point := by rw [hWid]

end MPP.Solutions.Bsd122
