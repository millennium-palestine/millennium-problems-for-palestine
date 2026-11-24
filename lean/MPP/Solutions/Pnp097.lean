import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp092
import MPP.Solutions.Pnp096

namespace MPP.Solutions.Pnp097

open Computability Turing MPP.PvsNP

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool,
    L (pair x w) = (decide (x.count true % 2 = 0) && decide (w.count true % 2 = 0)) := by
  obtain ⟨L1, h1, hL1⟩ := MPP.Solutions.Pnp096.main
  obtain ⟨L2, h2, hL2⟩ := MPP.Solutions.Pnp092.main
  refine ⟨fun z => L1 z && L2 z, MPP.Solutions.Pnp011.main L1 L2 h1 h2, ?_⟩
  intro x w
  simp only [hL1, hL2]

end MPP.Solutions.Pnp097
