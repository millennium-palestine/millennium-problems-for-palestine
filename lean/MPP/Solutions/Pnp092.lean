import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp091

namespace MPP.Solutions.Pnp092

open Computability Turing MPP.PvsNP

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = decide (w.count true % 2 = 0) := by
  obtain ⟨e, ⟨he⟩, hpair⟩ := MPP.Solutions.Pnp025.main
  refine ⟨fun z => decide ((e z).count true % 2 = 0), ?_, ?_⟩
  · exact MPP.Solutions.Pnp008.main _ e MPP.Solutions.Pnp091.main he
  · intro x w
    simp only [hpair]

end MPP.Solutions.Pnp092
