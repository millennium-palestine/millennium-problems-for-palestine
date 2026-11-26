import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp022
import MPP.Solutions.Pnp227

namespace MPP.Solutions.Pnp234

open Turing MPP.PvsNP

theorem main : ∀ h : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) →
    (∀ x : List Bool, h x = List.replicate (h x).length true) →
    ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = w.getD (h x).length false := by
  intro h hh hunary
  obtain ⟨r, hr, hreq⟩ := MPP.Solutions.Pnp022.main h hh
  obtain ⟨L, hL, hLeq⟩ := MPP.Solutions.Pnp227.main
  obtain ⟨hr'⟩ := hr
  obtain ⟨hL'⟩ := hL
  obtain ⟨c⟩ := MPP.Solutions.Pnp006.main hr' hL'
  refine ⟨L ∘ r, ⟨c⟩, fun x w => ?_⟩
  have key := hLeq (h x).length w
  rw [← hunary x] at key
  show L (r (pair x w)) = _
  rw [hreq x w]
  exact key

end MPP.Solutions.Pnp234
