import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp085
import MPP.Solutions.Pnp090

namespace MPP.Solutions.Pnp089

open Computability Turing MPP.PvsNP

theorem main : InP (fun x : List Bool => decide (x = x.reverse)) := by
  obtain ⟨L, hL, hpair⟩ := MPP.Solutions.Pnp085.main
  have hmap := (MPP.Solutions.Pnp090.main).some
  have h := MPP.Solutions.Pnp008.main L (fun x => pair x x.reverse) hL hmap
  convert h using 1
  funext x
  rw [hpair]
  simp [eq_comm]

end MPP.Solutions.Pnp089
