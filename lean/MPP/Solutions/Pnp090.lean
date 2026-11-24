import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp087

namespace MPP.Solutions.Pnp090

open Computability Turing MPP.PvsNP

theorem main : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
    (fun x : List Bool => pair x x.reverse : List Bool → List Bool)) := by
  obtain ⟨h, hh, heq⟩ := MPP.Solutions.Pnp026.main id List.reverse
    MPP.Solutions.Pnp037.main MPP.Solutions.Pnp087.main
  have hfun : h = fun x : List Bool => pair x x.reverse := funext fun z => heq z
  rw [← hfun]
  exact hh

end MPP.Solutions.Pnp090
