import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp052

namespace MPP.Solutions.Pnp127

open MPP.PvsNP Turing

/-- Pairing both outputs (pnp-026) and then concatenating the two components (pnp-052) gives the
concatenation of two polynomial-time maps. The composition is pnp-006. -/
theorem main : ∀ f g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) →
    ∃ h : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) ∧
      ∀ x : List Bool, h x = f x ++ g x := by
  intro f g hf hg
  obtain ⟨p, ⟨hp⟩, hpeq⟩ := MPP.Solutions.Pnp026.main f g hf hg
  obtain ⟨C, ⟨hC⟩, hCeq⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨hCp⟩ := MPP.Solutions.Pnp006.main hp hC
  refine ⟨C ∘ p, ⟨hCp⟩, fun x => ?_⟩
  simp only [Function.comp, hpeq, hCeq]

end MPP.Solutions.Pnp127
