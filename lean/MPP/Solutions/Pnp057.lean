import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp056

namespace MPP.Solutions.Pnp057

open MPP.PvsNP Turing

/-- One-bit extension of a polynomial-time language. The map `s` of pnp-056 sends `pair x u` to
`pair x (u ++ [false])`, and `z ↦ V (s z)` is in P by pnp-008. -/
theorem main : ∀ V : Lang, InP V → ∃ D : Lang, InP D ∧
    ∀ x u : List Bool, D (pair x u) = V (pair x (u ++ [false])) := by
  intro V hV
  obtain ⟨s, ⟨Ts⟩, hs_eq⟩ := MPP.Solutions.Pnp056.main
  refine ⟨fun z => V (s z), MPP.Solutions.Pnp008.main V s hV Ts, fun x u => ?_⟩
  simp only [hs_eq]

end MPP.Solutions.Pnp057
