import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp007
import MPP.Solutions.Pnp009

namespace MPP.Solutions.Pnp011

open MPP.PvsNP Turing

theorem main : ∀ L M : Lang, InP L → InP M → InP (fun x => L x && M x) := by
  intro L M hL hM
  obtain ⟨h9⟩ := MPP.Solutions.Pnp009.main L M hL hM
  obtain ⟨hand⟩ := MPP.Solutions.Pnp007.main
  obtain ⟨c⟩ := MPP.Solutions.Pnp006.main h9 hand
  exact Nonempty.intro c

end MPP.Solutions.Pnp011
