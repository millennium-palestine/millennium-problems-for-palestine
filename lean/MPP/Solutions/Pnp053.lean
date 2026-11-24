import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp052

namespace MPP.Solutions.Pnp053

open MPP.PvsNP Turing

/-- Flattening of a nested pair. The decoder `d` of pnp-021 takes the first component, the witness
projection `e` of pnp-025 takes the witness, and `cc` is the concatenation of pnp-052. The map
`y ↦ pair (d (d y)) (cc (pair (e (d y)) (e y)))` is polynomial-time by pnp-006 and pnp-026. -/
theorem main : ∃ r : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) r) ∧
      ∀ x u w : List Bool, r (pair (pair x u) w) = pair x (u ++ w) := by
  obtain ⟨d, ⟨Td⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨Te⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨cc, ⟨Tcc⟩, hcc_eq⟩ := MPP.Solutions.Pnp052.main
  -- K y = pair (e (d y)) (e y)
  obtain ⟨Ted⟩ := MPP.Solutions.Pnp006.main Td Te
  obtain ⟨K, ⟨TK⟩, hK_eq⟩ := MPP.Solutions.Pnp026.main (e ∘ d) e ⟨Ted⟩ ⟨Te⟩
  -- cc ∘ K
  obtain ⟨TcK⟩ := MPP.Solutions.Pnp006.main TK Tcc
  -- d ∘ d
  obtain ⟨Tdd⟩ := MPP.Solutions.Pnp006.main Td Td
  -- y ↦ pair (d (d y)) (cc (K y))
  obtain ⟨r, ⟨Tr⟩, hr_eq⟩ := MPP.Solutions.Pnp026.main (d ∘ d) (cc ∘ K) ⟨Tdd⟩ ⟨TcK⟩
  refine ⟨r, ⟨Tr⟩, fun x u w => ?_⟩
  rw [hr_eq]
  simp [Function.comp_apply, hK_eq, hd_eq, he_eq, hcc_eq]

end MPP.Solutions.Pnp053
