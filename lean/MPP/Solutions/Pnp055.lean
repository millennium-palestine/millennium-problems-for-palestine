import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp054

namespace MPP.Solutions.Pnp055

open MPP.PvsNP Turing

/-- Under `P = NP`, the prefix-extension language of pnp-054 is in P, since it is in NP. -/
theorem main : PEqualsNP → ∀ V : Lang, InP V → ∀ p : Polynomial ℕ, ∃ D : Lang, InP D ∧
    ∀ x u : List Bool, D (pair x u) = true ↔
      ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x (u ++ w)) = true := by
  intro hPNP V hV p
  obtain ⟨D, hDNP, hD⟩ := MPP.Solutions.Pnp054.main V hV p
  exact ⟨D, hPNP D hDNP, hD⟩

end MPP.Solutions.Pnp055
