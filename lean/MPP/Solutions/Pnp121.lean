import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp118
import MPP.Solutions.Pnp120

namespace MPP.Solutions.Pnp121

open MPP.PvsNP Turing

theorem main : ∀ g : Lang, InP g → ∀ k : ℕ, ∃ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
    ∀ x u : List Bool, s (pair x u) = pair x (u ++ [g ((x.drop u.length).take (k + 1))]) := by
  intro g hg k
  obtain ⟨D, ⟨hD⟩, hDeq⟩ := MPP.Solutions.Pnp120.main
  obtain ⟨T, ⟨hT⟩, hTeq⟩ := MPP.Solutions.Pnp118.main (k + 1)
  have hWD := MPP.Solutions.Pnp006.main hD hT
  obtain ⟨hWD'⟩ := hWD
  have hng : InP (fun y => !g y) := MPP.Solutions.Pnp004.main g hg
  have hL : InP (fun z => !g (T (D z))) :=
    MPP.Solutions.Pnp008.main (fun y => !g y) (T ∘ D) hng hWD'
  obtain ⟨s, ⟨hs⟩, hseq⟩ := MPP.Solutions.Pnp060.main (fun z => !g (T (D z))) hL
  refine ⟨s, ⟨hs⟩, fun x u => ?_⟩
  rw [hseq]
  simp only [Bool.not_not, hDeq, hTeq]
  simp [pair, List.append_assoc]

end MPP.Solutions.Pnp121
