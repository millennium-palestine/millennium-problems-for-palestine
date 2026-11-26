import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp231

namespace MPP.Solutions.Pnp233

open MPP.PvsNP Turing

theorem main : ∀ g : Lang, InP g →
    ∃ s : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
      ∀ x w : List Bool, s (pair x w) = pair x (w ++ [g ((w.reverse.take x.length).reverse)]) := by
  intro g hg
  obtain ⟨s1, ⟨hs1⟩, hs1z⟩ := MPP.Solutions.Pnp231.main g hg
  obtain ⟨d, ⟨hd⟩, hdx⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, hex⟩ := MPP.Solutions.Pnp025.main
  -- swap of the two components: pair x w ↦ pair w x
  obtain ⟨sw, ⟨hsw⟩, hswz⟩ := MPP.Solutions.Pnp026.main e d ⟨he⟩ ⟨hd⟩
  obtain ⟨h1⟩ := MPP.Solutions.Pnp006.main hsw hs1
  obtain ⟨h2⟩ := MPP.Solutions.Pnp006.main h1 hsw
  refine ⟨sw ∘ (s1 ∘ sw), ⟨h2⟩, fun x w => ?_⟩
  simp only [Function.comp_apply, hswz, hdx, hex, hs1z]

end MPP.Solutions.Pnp233
