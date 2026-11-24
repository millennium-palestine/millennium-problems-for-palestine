import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp038

namespace MPP.Solutions.Pnp039

open MPP.PvsNP Turing

theorem main : ∀ L : Lang, (∃ V : Lang, InP V ∧ ∀ x : List Bool, L x = V (pair x [])) → InP L := by
  rintro L ⟨V, hV, hL⟩
  obtain ⟨c⟩ := MPP.Solutions.Pnp038.main
  have h := MPP.Solutions.Pnp008.main V (fun x => pair x []) hV c
  have hfun : L = fun x => V (pair x []) := funext hL
  rw [hfun]
  exact h

end MPP.Solutions.Pnp039
