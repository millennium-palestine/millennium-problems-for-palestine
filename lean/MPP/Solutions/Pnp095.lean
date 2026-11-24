import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp087

namespace MPP.Solutions.Pnp095

open Computability Turing MPP.PvsNP

theorem main : ∀ L : List Bool → Bool, InP L → InP (fun x : List Bool => L x.reverse) := by
  intro L hL
  obtain ⟨h1⟩ := MPP.Solutions.Pnp087.main
  obtain ⟨h2⟩ := hL
  obtain ⟨h3⟩ := MPP.Solutions.Pnp006.main h1 h2
  exact ⟨h3⟩

end MPP.Solutions.Pnp095
