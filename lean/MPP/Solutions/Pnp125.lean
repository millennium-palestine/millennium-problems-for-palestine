import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp003
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp060

namespace MPP.Solutions.Pnp125

open MPP.PvsNP Turing

theorem main : ∀ (T : List Bool → List Bool) (b : Bool),
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) →
    ∃ T' : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T') ∧
      ∀ x : List Bool, T' x = T x ++ [b] := by
  intro T b hT
  -- the constant language `fun _ => !b` is in P
  have hD : InP (fun _ : List Bool => !b) := by
    cases b
    · exact MPP.Solutions.Pnp003.main
    · exact MPP.Solutions.Pnp004.main _ MPP.Solutions.Pnp003.main
  -- the append map of pnp-060 for this language
  obtain ⟨s, hs, hsv⟩ := MPP.Solutions.Pnp060.main (fun _ : List Bool => !b) hD
  obtain ⟨hT0⟩ := hT
  obtain ⟨hs0⟩ := hs
  refine ⟨s ∘ T, MPP.Solutions.Pnp006.main hT0 hs0, fun x => ?_⟩
  rw [Function.comp_apply, hsv (T x)]
  simp

end MPP.Solutions.Pnp125
