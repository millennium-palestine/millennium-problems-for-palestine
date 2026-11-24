import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp002
import MPP.Solutions.Pnp010

namespace MPP.Solutions.Pnp015

open MPP.PvsNP

theorem main : PEqualsNP → ∀ L M : Lang, InNP L → InNP M → InNP (fun x => L x || M x) := by
  intro hPNP L M hL hM
  have hPL : InP L := hPNP L hL
  have hPM : InP M := hPNP M hM
  exact MPP.Solutions.Pnp002.main (fun x => L x || M x) (MPP.Solutions.Pnp010.main L M hPL hPM)

end MPP.Solutions.Pnp015
