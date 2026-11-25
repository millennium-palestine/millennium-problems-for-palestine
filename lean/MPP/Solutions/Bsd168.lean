import Mathlib

namespace MPP.Solutions.Bsd168

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p))
    (Q : (W.baseChange (ZMod p)).toAffine.Point),
    let P := WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p)) Q
    let φ := WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
    φ (φ P) - (((p : ℤ) + 1 - (Nat.card (W.baseChange (ZMod p)).toAffine.Point : ℤ)) • φ P) + (p : ℤ) • P = 0 := by
  intro p _ _ W Q
  dsimp only
  have hfix : WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
      (WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p)) Q) =
      WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p)) Q :=
    WeierstrassCurve.Affine.Point.map_baseChange _ Q
  have hN : (Nat.card (W.baseChange (ZMod p)).toAffine.Point) • Q = 0 := card_nsmul_eq_zero'
  have hP : ((Nat.card (W.baseChange (ZMod p)).toAffine.Point : ℕ) : ℤ) •
      WeierstrassCurve.Affine.Point.baseChange (W' := W) (ZMod p) (AlgebraicClosure (ZMod p)) Q = 0 := by
    rw [natCast_zsmul, ← map_nsmul, hN, map_zero]
  rw [hfix, hfix]
  linear_combination (norm := module) hP

end MPP.Solutions.Bsd168
