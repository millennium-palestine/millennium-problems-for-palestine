import Mathlib
import MPP.Solutions.Bsd368

namespace MPP.Solutions.Bsd403

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    let φ := WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))
    Nat.card {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // φ P = P} =
      Nat.card W.toAffine.Point := by
  intro p _ _ W _ φ
  let ι : W.toAffine.Point → {P : (W.baseChange (AlgebraicClosure (ZMod p))).toAffine.Point // φ P = P} :=
    fun Q => ⟨WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) Q,
      (MPP.Solutions.Bsd368.main p W _).mpr ⟨Q, rfl⟩⟩
  have hinj : Function.Injective ι := fun Q1 Q2 h =>
    WeierstrassCurve.Affine.Point.map_injective (W' := W)
      (Algebra.ofId (ZMod p) (AlgebraicClosure (ZMod p))) (congrArg Subtype.val h)
  have hsurj : Function.Surjective ι := by
    rintro ⟨P, hP⟩
    obtain ⟨Q, hQ⟩ := (MPP.Solutions.Bsd368.main p W P).mp hP
    exact ⟨Q, Subtype.ext hQ⟩
  exact (Nat.card_congr (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).symm

end MPP.Solutions.Bsd403
