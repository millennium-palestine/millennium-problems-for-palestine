import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp037

namespace MPP.Solutions.Pnp038

open MPP.PvsNP Turing

theorem main : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) (fun x : List Bool => pair x [])) := by
  obtain ⟨g, hg, hgx⟩ := MPP.Solutions.Pnp030.main 0
  obtain ⟨h, hh, hz⟩ := MPP.Solutions.Pnp026.main id g MPP.Solutions.Pnp037.main hg
  have hg0 : ∀ x : List Bool, g x = [] := fun x => by
    rw [hgx x]
    rfl
  have hfun : (fun x : List Bool => pair x []) = h := funext fun z => by
    rw [hz z, hg0 z]
    rfl
  rw [hfun]
  exact hh

end MPP.Solutions.Pnp038
