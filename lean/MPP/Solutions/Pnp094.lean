import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp093

namespace MPP.Solutions.Pnp094

open Computability Turing MPP.PvsNP

theorem main : ∃ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x w : List Bool, f (pair x w) = List.replicate (w.count true) true := by
  obtain ⟨e, ⟨he⟩, hpe⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨hc⟩ := MPP.Solutions.Pnp093.main
  obtain ⟨hcomp⟩ := MPP.Solutions.Pnp006.main he hc
  refine ⟨(fun x : List Bool => List.replicate (x.count true) true) ∘ e, ⟨hcomp⟩, fun x w => ?_⟩
  simp [Function.comp, hpe x w]

end MPP.Solutions.Pnp094
