import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp014

namespace MPP.Solutions.Pnp017

open MPP.PvsNP

theorem main : PEqualsNP → ∀ L : Lang, InNP L → InNP (fun x => !L x) := by
  intro hPNP L hL
  exact MPP.Solutions.Pnp014.main L (hPNP L hL)

end MPP.Solutions.Pnp017
