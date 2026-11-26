import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp060
import MPP.Solutions.Pnp127
import MPP.Solutions.Pnp230

namespace MPP.Solutions.Pnp231

open MPP.PvsNP Turing

theorem main : ∀ g : Lang, InP g →
    ∃ s : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) ∧
      ∀ w x : List Bool, s (pair w x) = pair (w ++ [g ((w.reverse.take x.length).reverse)]) x := by
  intro g hg
  obtain ⟨T, ⟨hT⟩, hTeq⟩ := MPP.Solutions.Pnp230.main
  -- z ↦ !g (T z) is in P, so z ↦ [g (T z)] is a polynomial-time map to one-bit lists
  have hL : InP (fun y => !g y) := MPP.Solutions.Pnp004.main g hg
  have hLT : InP (fun z => !g (T z)) := MPP.Solutions.Pnp008.main (fun y => !g y) T hL hT
  obtain ⟨hLT'⟩ := hLT
  obtain ⟨hW⟩ := MPP.Solutions.Pnp060.negWrapComp
  obtain ⟨hB⟩ := MPP.Solutions.Pnp006.main hLT' hW
  have hB' : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (id : List Bool → List Bool) (fun z => [g (T z)])) := by
    have e : ((fun b : Bool => [!b]) ∘ (fun y => !g (T y))) = (fun z => [g (T z)]) := by
      funext z
      simp
    rw [e] at hB
    exact ⟨hB⟩
  -- the first component is the decoding of w, with the new bit appended
  obtain ⟨d, ⟨hd⟩, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨e, ⟨he⟩, heq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨h1, ⟨hh1⟩, hh1eq⟩ := MPP.Solutions.Pnp127.main d (fun z => [g (T z)]) ⟨hd⟩ hB'
  obtain ⟨s, ⟨hs⟩, hseq⟩ := MPP.Solutions.Pnp026.main h1 e ⟨hh1⟩ ⟨he⟩
  refine ⟨s, ⟨hs⟩, fun w x => ?_⟩
  simp only [hseq, hh1eq, hdeq, heq, hTeq]

end MPP.Solutions.Pnp231
