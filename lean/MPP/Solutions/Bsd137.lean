import Mathlib
import MPP.Solutions.Bsd130
import MPP.Solutions.Bsd134

namespace MPP.Solutions.Bsd137

theorem main : ∀ (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Function.Bijective ⇑(WeierstrassCurve.Affine.Point.map (W' := W)
      (FiniteField.frobeniusAlgHom (ZMod p) (AlgebraicClosure (ZMod p)))) := by
  intro p _ _ W _
  -- injective by bsd-130, surjective by bsd-134
  exact ⟨fun P Q h => MPP.Solutions.Bsd130.main p W P Q h,
    fun Q => MPP.Solutions.Bsd134.main p W Q⟩

end MPP.Solutions.Bsd137
