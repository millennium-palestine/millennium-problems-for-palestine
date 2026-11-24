import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp092

namespace MPP.Solutions.Pnp099

open Computability Turing MPP.PvsNP

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = decide (w.count true % 2 ≠ 0) := by
  obtain ⟨L1, h1, hL1⟩ := MPP.Solutions.Pnp092.main
  refine ⟨fun z => !L1 z, MPP.Solutions.Pnp004.main L1 h1, ?_⟩
  intro x w
  rcases Nat.mod_two_eq_zero_or_one (w.count true) with h | h <;> simp [hL1, h]

end MPP.Solutions.Pnp099
