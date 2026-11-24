import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp049

namespace MPP.Solutions.Pnp076

open MPP.PvsNP Turing

theorem main : PEqualsNP → ∀ (V : Lang) (p : Polynomial ℕ), InP V → ∀ L : Lang,
    (∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
    InP L := by
  intro hPNP V p hV L hL
  exact hPNP L (MPP.Solutions.Pnp049.main L ⟨V, hV, p, hL⟩)

end MPP.Solutions.Pnp076
