import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp052

namespace MPP.Solutions.Pnp060

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- The bit negation machine of pnp-004 has output the one-bit list [!b] on its
single stack, so it also computes b ↦ [!b] when the output is read as a list. -/
theorem negWrapComp :
    Nonempty (TM2ComputableInPolyTime encodeBool (id : List Bool → List Bool) (fun b : Bool => [!b])) := by
  refine ⟨{ tm := MPP.Solutions.Pnp004.negMachine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨1, ?_⟩, ?_⟩
  · cases a <;> rfl
  · simp

theorem main : ∀ D : Lang, InP D → ∃ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
    ∀ z : List Bool, s z = z ++ [!D z] := by
  intro D hD
  obtain ⟨hD'⟩ := hD
  obtain ⟨hW⟩ := negWrapComp
  -- z ↦ [!D z], by composing the decider with the wrapped negation
  have hg : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun z => [!D z])) := by
    obtain ⟨hg'⟩ := MPP.Solutions.Pnp006.main hD' hW
    exact ⟨hg'⟩
  -- z ↦ pair z [!D z]
  obtain ⟨h, hh, hhz⟩ := MPP.Solutions.Pnp026.main id (fun z => [!D z])
    MPP.Solutions.Pnp037.main hg
  -- pair z [!D z] ↦ z ++ [!D z], by the concatenation of pnp-052
  obtain ⟨C, hC, hCeq⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨hh'⟩ := hh
  obtain ⟨hC'⟩ := hC
  refine ⟨C ∘ h, MPP.Solutions.Pnp006.main hh' hC', fun z => ?_⟩
  show C (h z) = z ++ [!D z]
  rw [hhz z]
  exact hCeq z [!D z]

end MPP.Solutions.Pnp060
