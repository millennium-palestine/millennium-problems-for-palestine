import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp044

namespace MPP.Solutions.Pnp077

open MPP.PvsNP Turing

theorem main : (∀ (V : Lang) (p : Polynomial ℕ), InP V → ∀ L : Lang,
    (∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
    InP L) →
  PEqualsNP := by
  intro H L hL
  obtain ⟨V, hV, p, hL'⟩ := MPP.Solutions.Pnp044.main L hL
  exact H V p hV L hL'

end MPP.Solutions.Pnp077
