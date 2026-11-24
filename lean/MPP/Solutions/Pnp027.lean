import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp022
import MPP.Solutions.Pnp028
import MPP.Solutions.Pnp033

namespace MPP.Solutions.Pnp027

open MPP.PvsNP Turing

theorem main : ∀ p : Polynomial ℕ, ∃ C : List Bool → Bool,
    InP C ∧ ∀ x w : List Bool, C (pair x w) = true ↔ w.length ≤ p.eval x.length := by
  intro p
  obtain ⟨g, ⟨hg⟩, hgx⟩ := MPP.Solutions.Pnp033.main p
  obtain ⟨r, ⟨hr⟩, hrz⟩ := MPP.Solutions.Pnp022.main g ⟨hg⟩
  obtain ⟨Q, hQ, hQiff⟩ := MPP.Solutions.Pnp028.main
  refine ⟨fun z => Q (r z), MPP.Solutions.Pnp008.main Q r hQ hr, fun x w => ?_⟩
  simp only [hrz, hQiff, hgx, List.length_replicate]

end MPP.Solutions.Pnp027
