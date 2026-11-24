import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006

namespace MPP.Solutions.Pnp020

open MPP.PvsNP Turing

theorem main : ∀ S T : Lang,
    (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ x, L x = S (f x)) →
    (∃ g : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) ∧
        ∀ x, S x = T (g x)) →
    (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ x, L x = T (f x)) := by
  intro S T hS hST L hL
  obtain ⟨f, ⟨hf⟩, hLf⟩ := hS L hL
  obtain ⟨g, ⟨hg⟩, hSg⟩ := hST
  obtain ⟨c⟩ := MPP.Solutions.Pnp006.main hf hg
  exact ⟨g ∘ f, ⟨c⟩, fun x => (hLf x).trans (hSg (f x))⟩

end MPP.Solutions.Pnp020
