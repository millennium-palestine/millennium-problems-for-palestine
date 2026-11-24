import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp039

namespace MPP.Solutions.Pnp040

open MPP.PvsNP Turing

theorem main : ∀ L : Lang, InP L ↔ ∃ V : Lang, InP V ∧ ∀ x : List Bool, L x = V (pair x []) := by
  intro L
  constructor
  · intro hL
    obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
    refine ⟨fun y => L (d y), MPP.Solutions.Pnp008.main L d hL hd, fun x => ?_⟩
    show L x = L (d (pair x []))
    rw [hdx x []]
  · rintro ⟨V, hV, hL⟩
    exact MPP.Solutions.Pnp039.main L ⟨V, hV, hL⟩

end MPP.Solutions.Pnp040
