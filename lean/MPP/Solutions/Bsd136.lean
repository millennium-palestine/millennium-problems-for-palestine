import Mathlib

namespace MPP.Solutions.Bsd136

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P Q : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) (P + Q) =
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P +
    WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) Q := by
  intro p _ _ W _ P Q
  -- `Point.map` is an additive monoid homomorphism
  exact map_add (WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))) P Q

end MPP.Solutions.Bsd136
