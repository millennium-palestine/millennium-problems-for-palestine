import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp004
import MPP.Solutions.Pnp091

namespace MPP.Solutions.Pnp098

open Computability Turing MPP.PvsNP

theorem main : InP (fun x : List Bool => decide (x.count true % 2 ≠ 0)) := by
  have h := MPP.Solutions.Pnp004.main _ MPP.Solutions.Pnp091.main
  have e : (fun x : List Bool => !decide (x.count true % 2 = 0)) =
      (fun x : List Bool => decide (x.count true % 2 ≠ 0)) := by
    funext x
    rcases Nat.mod_two_eq_zero_or_one (x.count true) with h | h <;> simp [h]
  rw [e] at h
  exact h

end MPP.Solutions.Pnp098
