import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp002
import MPP.Solutions.Pnp014

namespace MPP.Solutions.Pnp048

open MPP.PvsNP

theorem main : ∀ L : Lang, InP L → InNP L ∧ InNP (fun x => !L x) := by
  intro L hL
  exact ⟨MPP.Solutions.Pnp002.main L hL, MPP.Solutions.Pnp014.main L hL⟩

end MPP.Solutions.Pnp048
