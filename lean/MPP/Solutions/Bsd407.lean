import Mathlib
import MPP.Solutions.Bsd406

namespace MPP.Solutions.Bsd407

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    let φ := WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
    (Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // (1 : ℤ) • P - (1 : ℤ) • φ P = 0} : ℤ) =
      (1 : ℤ) ^ 2 - ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) * 1 * 1 + (p : ℤ) * 1 ^ 2 := by
  intro p _ _ W _ φ
  have hfix : Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // (1 : ℤ) • P - (1 : ℤ) • φ P = 0} =
      Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point //
        WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro P
    simp only [one_smul, sub_eq_zero]
    exact eq_comm
  rw [hfix, MPP.Solutions.Bsd406.main p W]
  ring

end MPP.Solutions.Bsd407
