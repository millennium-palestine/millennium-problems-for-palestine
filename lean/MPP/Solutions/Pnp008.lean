import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006

namespace MPP.Solutions.Pnp008

open MPP.PvsNP Turing

theorem main : ∀ (L : Lang) (f : List Bool → List Bool),
    InP L → TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f →
      InP (fun x => L (f x)) := by
  intro L f hL hf
  obtain ⟨hL'⟩ := hL
  obtain ⟨c⟩ := MPP.Solutions.Pnp006.main hf hL'
  exact ⟨c⟩

end MPP.Solutions.Pnp008
