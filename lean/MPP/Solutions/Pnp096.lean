import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp091

namespace MPP.Solutions.Pnp096

open Computability Turing MPP.PvsNP

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = decide (x.count true % 2 = 0) := by
  obtain ⟨d, ⟨hd⟩, hpair⟩ := MPP.Solutions.Pnp021.main
  refine ⟨fun z => decide ((d z).count true % 2 = 0), ?_, ?_⟩
  · exact MPP.Solutions.Pnp008.main _ d MPP.Solutions.Pnp091.main hd
  · intro x w
    simp only [hpair]

end MPP.Solutions.Pnp096
