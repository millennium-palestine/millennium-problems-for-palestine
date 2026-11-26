import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp134

namespace MPP.Solutions.Pnp227

open Turing MPP.PvsNP

theorem main : ∃ L : Lang, InP L ∧ ∀ (m : ℕ) (w : List Bool),
    L (pair (List.replicate m true) w) = w.getD m false := by
  obtain ⟨L, hL, hEq⟩ := MPP.Solutions.Pnp134.main
  refine ⟨L, hL, fun m w => ?_⟩
  rw [hEq, List.count_replicate_self]

end MPP.Solutions.Pnp227
