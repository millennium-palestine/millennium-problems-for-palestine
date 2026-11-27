import Mathlib
import MPP.Solutions.Bsd368

namespace MPP.Solutions.Bsd406

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} =
      Nat.card W.toAffine.Point := by
  intro p _ _ W _
  let ι := WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
  let f : W.toAffine.Point → {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} :=
    fun Q => ⟨ι Q, (MPP.Solutions.Bsd368.main p W (ι Q)).mpr ⟨Q, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro Q1 Q2 h
      exact WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
        (congrArg Subtype.val h)
    · rintro ⟨P, hP⟩
      obtain ⟨Q, hQ⟩ := (MPP.Solutions.Bsd368.main p W P).mp hP
      exact ⟨Q, Subtype.ext hQ⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end MPP.Solutions.Bsd406
