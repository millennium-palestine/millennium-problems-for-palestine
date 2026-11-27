import Mathlib
import MPP.Solutions.Bsd368

namespace MPP.Solutions.Bsd369

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} =
    Nat.card W.toAffine.Point := by
  intro p _ _ W _
  let g : W.toAffine.Point → {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
      WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} :=
    fun Q => ⟨WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) Q,
      (MPP.Solutions.Bsd368.main p W _).mpr ⟨Q, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro Q1 Q2 h
      exact WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
        (congrArg Subtype.val h)
    · rintro ⟨P, hP⟩
      obtain ⟨Q, hQ⟩ := (MPP.Solutions.Bsd368.main p W P).mp hP
      exact ⟨Q, Subtype.ext hQ⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

end MPP.Solutions.Bsd369
