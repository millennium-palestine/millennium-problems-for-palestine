import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp234

namespace MPP.Solutions.Pnp236

open Turing MPP.PvsNP

theorem main : ∀ a b : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    (∀ x : List Bool, a x = List.replicate (a x).length true) →
    (∀ x : List Bool, b x = List.replicate (b x).length true) →
    ∃ L : Lang, InP L ∧ ∀ x w : List Bool,
      L (pair x w) = (w.getD (a x).length false && w.getD (b x).length false) := by
  intro a b ha hb ua ub
  obtain ⟨L1, hL1, e1⟩ := MPP.Solutions.Pnp234.main a ha ua
  obtain ⟨L2, hL2, e2⟩ := MPP.Solutions.Pnp234.main b hb ub
  refine ⟨fun y => L1 y && L2 y, MPP.Solutions.Pnp011.main L1 L2 hL1 hL2, fun x w => ?_⟩
  dsimp only
  rw [e1 x w, e2 x w]

end MPP.Solutions.Pnp236
