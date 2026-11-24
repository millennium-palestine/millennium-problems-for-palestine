import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp052

namespace MPP.Solutions.Pnp056

open MPP.PvsNP Turing

/-- One-bit extension. The decoder `d` of pnp-021 takes the first component, the witness projection
`e` of pnp-025 takes the second, `c` of pnp-030 with length 1 outputs `[false]`, and `cc` is the
concatenation of pnp-052. The map `z ↦ pair (d z) (cc (pair (e z) (c z)))` is polynomial-time by
pnp-006 and pnp-026. -/
theorem main : ∃ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
      ∀ x u : List Bool, s (pair x u) = pair x (u ++ [false]) := by
  obtain ⟨d, ⟨Td⟩, hd_eq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨Te⟩, he_eq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨cc, ⟨Tcc⟩, hcc_eq⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨c, ⟨Tc⟩, hc_eq⟩ := MPP.Solutions.Pnp030.main 1
  -- g z = pair (e z) (c z)
  obtain ⟨g, ⟨Tg⟩, hg_eq⟩ := MPP.Solutions.Pnp026.main e c ⟨Te⟩ ⟨Tc⟩
  -- cc ∘ g
  obtain ⟨Tcg⟩ := MPP.Solutions.Pnp006.main Tg Tcc
  -- z ↦ pair (d z) (cc (g z))
  obtain ⟨s, ⟨Ts⟩, hs_eq⟩ := MPP.Solutions.Pnp026.main d (cc ∘ g) ⟨Td⟩ ⟨Tcg⟩
  refine ⟨s, ⟨Ts⟩, fun x u => ?_⟩
  rw [hs_eq]
  simp [Function.comp_apply, hd_eq, hg_eq, he_eq, hc_eq, hcc_eq]

end MPP.Solutions.Pnp056
