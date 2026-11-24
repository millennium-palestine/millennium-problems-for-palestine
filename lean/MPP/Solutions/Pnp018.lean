import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008

namespace MPP.Solutions.Pnp018

open MPP.PvsNP Turing

theorem main : ∀ S : Lang, (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x, L x = S (f x)) → InP S → PEqualsNP := by
  intro S hard hS L hL
  obtain ⟨f, hf, hLf⟩ := hard L hL
  obtain ⟨hf'⟩ := hf
  have h := MPP.Solutions.Pnp008.main S f hS hf'
  have hEq : L = fun x => S (f x) := funext fun x => hLf x
  rw [hEq]
  exact h

end MPP.Solutions.Pnp018
