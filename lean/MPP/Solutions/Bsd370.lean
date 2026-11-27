import Mathlib

namespace MPP.Solutions.Bsd370

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = 0 → P = 0 := by
  intro p _ _ W _ P h
  apply WeierstrassCurve.Affine.Point.map_injective (W' := W)
    (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
  rw [h, WeierstrassCurve.Affine.Point.map_zero]

end MPP.Solutions.Bsd370
