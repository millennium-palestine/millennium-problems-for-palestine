import Mathlib

namespace MPP.Solutions.Bsd371

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (Q : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    ∃ P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = Q := by
  intro p _ _ W _ Q
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfp : ∀ z : AlgebraicClosure (ZMod p),
      FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) z = z ^ p := by
    intro z
    simp [ZMod.card]
  have hsurj : ∀ x : AlgebraicClosure (ZMod p), ∃ u : AlgebraicClosure (ZMod p), u ^ p = x := by
    intro x
    have hb : Function.Bijective (fun z : AlgebraicClosure (ZMod p) => z ^ p) :=
      PerfectRing.bijective_frobenius
    obtain ⟨u, hu⟩ := hb.2 x
    exact ⟨u, hu⟩
  rcases Q with _ | ⟨x, y, h⟩
  · exact ⟨0, WeierstrassCurve.Affine.Point.map_zero _⟩
  · obtain ⟨u, rfl⟩ := hsurj x
    obtain ⟨v, rfl⟩ := hsurj y
    set f := FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) with hf
    set A := W.baseChange (AlgebraicClosure (ZMod p)) with hA
    have ha1 : f A.a₁ = A.a₁ := f.commutes _
    have ha2 : f A.a₂ = A.a₂ := f.commutes _
    have ha3 : f A.a₃ = A.a₃ := f.commutes _
    have ha4 : f A.a₄ = A.a₄ := f.commutes _
    have ha6 : f A.a₆ = A.a₆ := f.commutes _
    -- the curve equation and the nonsingularity of (u^p, v^p) are transported back along f
    have hnsh := (WeierstrassCurve.Affine.nonsingular_iff' _ _).mp h
    have heq := (WeierstrassCurve.Affine.equation_iff' _ _).mp hnsh.1
    have hdis := hnsh.2
    have hE : f (v ^ 2 + A.a₁ * u * v + A.a₃ * v - (u ^ 3 + A.a₂ * u ^ 2 + A.a₄ * u + A.a₆)) =
        (v ^ p) ^ 2 + A.a₁ * u ^ p * v ^ p + A.a₃ * v ^ p -
          ((u ^ p) ^ 3 + A.a₂ * (u ^ p) ^ 2 + A.a₄ * u ^ p + A.a₆) := by
      simp only [map_sub, map_add, map_mul, map_pow, ha1, ha2, ha3, ha4, ha6]
      simp only [hfp]
    have hEu : v ^ 2 + A.a₁ * u * v + A.a₃ * v - (u ^ 3 + A.a₂ * u ^ 2 + A.a₄ * u + A.a₆) = 0 := by
      have h0 : f (v ^ 2 + A.a₁ * u * v + A.a₃ * v - (u ^ 3 + A.a₂ * u ^ 2 + A.a₄ * u + A.a₆)) = 0 := by
        rw [hE]
        exact heq
      rw [hfp] at h0
      exact (pow_eq_zero_iff hp0).mp h0
    have hD1 : f (A.a₁ * v - (3 * u ^ 2 + 2 * A.a₂ * u + A.a₄)) =
        A.a₁ * v ^ p - (3 * (u ^ p) ^ 2 + 2 * A.a₂ * u ^ p + A.a₄) := by
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, ha1, ha2, ha4]
      simp only [hfp]
    have hD2 : f (2 * v + A.a₁ * u + A.a₃) = 2 * v ^ p + A.a₁ * u ^ p + A.a₃ := by
      simp only [map_add, map_mul, map_ofNat, ha1, ha3]
      simp only [hfp]
    have hnon : A.toAffine.Nonsingular u v := by
      rw [WeierstrassCurve.Affine.nonsingular_iff']
      refine ⟨(WeierstrassCurve.Affine.equation_iff' _ _).mpr hEu, ?_⟩
      rcases hdis with hd | hd
      · left
        intro h0
        apply hd
        rw [← hD1, h0, map_zero]
      · right
        intro h0
        apply hd
        rw [← hD2, h0, map_zero]
    refine ⟨WeierstrassCurve.Affine.Point.some _ _ hnon, ?_⟩
    rw [WeierstrassCurve.Affine.Point.map_some]
    congr 1 <;> exact hfp _

end MPP.Solutions.Bsd371
