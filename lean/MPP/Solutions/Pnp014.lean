import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp002
import MPP.Solutions.Pnp004

namespace MPP.Solutions.Pnp014

open MPP.PvsNP

theorem main : ∀ L : Lang, InP L → InNP (fun x => !L x) := by
  intro L hL
  exact MPP.Solutions.Pnp002.main (fun x => !L x) (MPP.Solutions.Pnp004.main L hL)

end MPP.Solutions.Pnp014
