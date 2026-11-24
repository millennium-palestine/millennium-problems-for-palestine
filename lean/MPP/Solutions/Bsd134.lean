import Mathlib

namespace MPP.Solutions.Bsd134

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (Q : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    ∃ P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point,
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = Q := by
  intro p _ _ W _ Q
  -- the Frobenius on the algebraic closure is the p-th power map
  have hF : ∀ z : AlgebraicClosure (ZMod p),
      FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) z = z ^ p := by
    intro z
    simp [ZMod.card]
  cases Q with
  | zero => exact ⟨0, WeierstrassCurve.Affine.Point.map_zero _⟩
  | some x y h =>
    -- the algebraic closure is algebraically closed, so every coordinate has a p-th root
    obtain ⟨x', hx'⟩ := IsAlgClosed.exists_pow_nat_eq x (Fact.out : p.Prime).pos
    obtain ⟨y', hy'⟩ := IsAlgClosed.exists_pow_nat_eq y (Fact.out : p.Prime).pos
    subst hx' hy'
    -- the point (x', y') is nonsingular, because its Frobenius image (x'^p, y'^p) is
    have hFn : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) x')
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)) y') := by
      rw [hF, hF]
      exact h
    have hn : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Nonsingular x' y' :=
      (WeierstrassCurve.Affine.baseChange_nonsingular W
        (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))).toRingHom.injective x' y').mp hFn
    exact ⟨WeierstrassCurve.Affine.Point.some x' y' hn, by
      simp only [WeierstrassCurve.Affine.Point.map_some, hF]⟩

end MPP.Solutions.Bsd134
