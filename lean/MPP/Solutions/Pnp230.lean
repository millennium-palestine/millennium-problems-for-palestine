import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp022
import MPP.Solutions.Pnp087
import MPP.Solutions.Pnp136

namespace MPP.Solutions.Pnp230

open MPP.PvsNP Turing

theorem main : ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ w x : List Bool, T (pair w x) = (w.reverse.take x.length).reverse := by
  obtain ⟨r, ⟨hr⟩, hrz⟩ := MPP.Solutions.Pnp022.main List.reverse MPP.Solutions.Pnp087.main
  obtain ⟨t, ⟨ht⟩, htz⟩ := MPP.Solutions.Pnp136.main
  obtain ⟨hc⟩ := MPP.Solutions.Pnp087.main
  obtain ⟨h1⟩ := MPP.Solutions.Pnp006.main hr ht
  obtain ⟨h2⟩ := MPP.Solutions.Pnp006.main h1 hc
  refine ⟨List.reverse ∘ (t ∘ r), ⟨h2⟩, fun w x => ?_⟩
  show List.reverse (t (r (pair w x))) = _
  rw [hrz w x, htz]

end MPP.Solutions.Pnp230
