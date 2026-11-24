import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp033
import MPP.Solutions.Pnp037

namespace MPP.Solutions.Pnp046

open MPP.PvsNP Turing

theorem main : ∀ p : Polynomial ℕ, ∃ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
    ∀ x : List Bool, f x = pair x (List.replicate (p.eval x.length) false) := by
  intro p
  obtain ⟨g, ⟨hg⟩, hgx⟩ := MPP.Solutions.Pnp033.main p
  obtain ⟨h, ⟨hh⟩, hhz⟩ :=
    MPP.Solutions.Pnp026.main (id : List Bool → List Bool) g MPP.Solutions.Pnp037.main ⟨hg⟩
  exact ⟨h, ⟨hh⟩, fun x => by rw [hhz, hgx]; rfl⟩

end MPP.Solutions.Pnp046
