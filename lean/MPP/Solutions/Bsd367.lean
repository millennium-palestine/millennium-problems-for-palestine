import Mathlib

namespace MPP.Solutions.Bsd367

theorem main : ∀ (p : ℕ) [Fact p.Prime] (x : AlgebraicClosure (ZMod p)), x ^ p = x →
    ∃ a : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a = x := by
  intro p _ x hx
  classical
  by_contra hne
  have hne' : ∀ a : ZMod p, algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) a ≠ x :=
    fun a h => hne ⟨a, h⟩
  have hdeg : ((Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).natDegree = p := by
    rw [Polynomial.natDegree_map]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) (Fact.out : p.Prime).one_lt
  have hf0 : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact (Fact.out : p.Prime).ne_zero hdeg.symm
  have hinj : Function.Injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) :=
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  have hximg : x ∉ Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact hne' a ha
  have hcard : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).card
      = p + 1 := by
    rw [Finset.card_insert_of_notMem hximg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      ZMod.card]
  have hroot : ∀ z ∈ insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))),
      ((Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot z := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hzx | hz
    · rw [hzx, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
      simp [hx]
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
      rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
      simp [Polynomial.aeval_X_pow, ← map_pow, ZMod.pow_card]
  have hsub : (insert x (Finset.univ.image (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))).val ⊆
      ((Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).map
        (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).roots := fun z hz =>
    (Polynomial.mem_roots hf0).mpr (hroot z (Finset.mem_val.mp hz))
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  omega

end MPP.Solutions.Bsd367
