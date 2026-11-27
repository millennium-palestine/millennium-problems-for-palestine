import Mathlib
import MPP.Solutions.Bsd367

namespace MPP.Solutions.Bsd368

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic]
    (P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point),
    WeierstrassCurve.Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) P = P ↔
      ∃ Q : W.toAffine.Point, WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) Q = P := by
  intro p _ _ W _ P
  constructor
  · intro hP
    cases P with
    | zero => exact ⟨0, rfl⟩
    | some x y h =>
      rw [WeierstrassCurve.Affine.Point.map_some] at hP
      obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hP
      have hx' : x ^ p = x := by
        have h2 : x ^ Fintype.card (ZMod p) = x := hx
        rwa [ZMod.card] at h2
      have hy' : y ^ p = y := by
        have h2 : y ^ Fintype.card (ZMod p) = y := hy
        rwa [ZMod.card] at h2
      obtain ⟨a, rfl⟩ := MPP.Solutions.Bsd367.main p x hx'
      obtain ⟨b, rfl⟩ := MPP.Solutions.Bsd367.main p y hy'
      have hK : Function.Injective (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) :=
        (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))).injective
      have hQ : W.toAffine.Nonsingular a b :=
        (WeierstrassCurve.Affine.baseChange_nonsingular W hK a b).mp h
      exact ⟨WeierstrassCurve.Affine.Point.some a b hQ, rfl⟩
  · rintro ⟨Q, rfl⟩
    have hsub : ∀ φ ψ : ZMod p →ₐ[ZMod p] AlgebraicClosure (ZMod p), φ = ψ :=
      fun φ ψ => Subsingleton.elim φ ψ
    exact (WeierstrassCurve.Affine.Point.map_map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p)))
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p))) Q).trans
      (congrArg (fun φ => WeierstrassCurve.Affine.Point.map (W' := W) φ Q) (hsub _ _))

end MPP.Solutions.Bsd368
