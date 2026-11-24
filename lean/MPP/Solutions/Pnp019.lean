import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp019

open MPP.PvsNP Turing

theorem main : ∀ S : Lang, InNP S → (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x, L x = S (f x)) → ¬ InP S → ¬ PEqualsNP := by
  intro S hS _ hnot hPNP
  exact hnot (hPNP S hS)

end MPP.Solutions.Pnp019
