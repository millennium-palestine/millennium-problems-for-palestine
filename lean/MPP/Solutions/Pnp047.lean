import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp018

namespace MPP.Solutions.Pnp047

open MPP.PvsNP Turing

theorem main : ∀ S : Lang, (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x, L x = S (f x)) → ¬ PEqualsNP → ¬ InP S := by
  intro S hard hNP hS
  exact hNP (MPP.Solutions.Pnp018.main S hard hS)

end MPP.Solutions.Pnp047
