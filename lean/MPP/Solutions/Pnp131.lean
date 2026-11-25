import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp130

namespace MPP.Solutions.Pnp131

open MPP.PvsNP Computability Turing

/-- Under P = NP, the windowed-witness language of pnp-130 is in P: its NP membership gives
membership in P, and the characterisation of pnp-130 is kept. -/
theorem main : PEqualsNP → ∀ g : Lang, InP g → ∀ k : ℕ, ∃ S : Lang, InP S ∧ ∀ x : List Bool, S x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ∧
      ∀ i : ℕ, i + (k + 1) ≤ (x ++ w).length → g (((x ++ w).drop i).take (k + 1)) = true := by
  intro h g hg k
  obtain ⟨S, hS, hchar⟩ := MPP.Solutions.Pnp130.main g hg k
  exact ⟨S, h S hS, hchar⟩

end MPP.Solutions.Pnp131
