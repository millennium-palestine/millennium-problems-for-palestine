import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008

namespace MPP.Solutions.Pnp036

open MPP.PvsNP Turing

theorem main : ∀ (S L : Lang) (f : List Bool → List Bool),
    InP S → TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f →
      (∀ x, L x = S (f x)) → InP L := by
  intro S L f hS hf hL
  have h := MPP.Solutions.Pnp008.main S f hS hf
  have hfun : L = fun x => S (f x) := funext hL
  rw [hfun]
  exact h

end MPP.Solutions.Pnp036
