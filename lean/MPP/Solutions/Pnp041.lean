import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp041

open MPP.PvsNP

theorem main : ¬ PEqualsNP ↔ ∃ L : Lang, InNP L ∧ ¬ InP L := by
  unfold PEqualsNP
  simp only [not_forall, exists_prop]

end MPP.Solutions.Pnp041
