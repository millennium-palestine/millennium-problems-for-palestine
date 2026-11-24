import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026

namespace MPP.Solutions.Pnp022

open MPP.PvsNP Turing

theorem main : ∀ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) →
    ∃ r : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) r) ∧
      ∀ x w : List Bool, r (pair x w) = pair (f x) w := by
  intro f hf
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hf0⟩ := hf
  obtain ⟨hfd⟩ := MPP.Solutions.Pnp006.main hd hf0
  obtain ⟨r, hr, hrz⟩ := MPP.Solutions.Pnp026.main (f ∘ d) e ⟨hfd⟩ ⟨he⟩
  refine ⟨r, hr, fun x w => ?_⟩
  rw [hrz]
  simp only [Function.comp_apply, hdx, hex]

end MPP.Solutions.Pnp022
