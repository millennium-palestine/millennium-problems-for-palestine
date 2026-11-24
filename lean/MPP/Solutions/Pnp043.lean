import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp003

namespace MPP.Solutions.Pnp043

open MPP.PvsNP Turing

theorem main : (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x, L x = (fun _ => true) (f x)) → PEqualsNP := by
  intro h
  unfold PEqualsNP
  intro L hL
  obtain ⟨f, _, hf⟩ := h L hL
  have hL' : L = fun _ => true := by
    funext x
    rw [hf x]
  rw [hL']
  exact MPP.Solutions.Pnp003.main

end MPP.Solutions.Pnp043
