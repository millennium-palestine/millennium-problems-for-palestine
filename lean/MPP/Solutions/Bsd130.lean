import Mathlib

namespace MPP.Solutions.Bsd130

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P Q : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P =
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) Q → P = Q := by
  intro p _ _ W _ P Q h
  exact (WeierstrassCurve.Affine.Point.map_injective (W' := W)
    (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))) h

end MPP.Solutions.Bsd130
