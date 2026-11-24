import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp085

namespace MPP.Solutions.Pnp086

open MPP.PvsNP Turing

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = decide (w ≠ x) := by
  obtain ⟨L, hL, hEq⟩ := MPP.Solutions.Pnp085.main
  refine ⟨fun z => !L z, MPP.Solutions.Pnp004.main L hL, fun x w => ?_⟩
  simp [hEq]

end MPP.Solutions.Pnp086
