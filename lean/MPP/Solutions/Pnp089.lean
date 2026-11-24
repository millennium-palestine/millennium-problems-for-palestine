import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp085
import MPP.Solutions.Pnp090

namespace MPP.Solutions.Pnp089

open Computability Turing MPP.PvsNP

theorem main : InP (fun x : List Bool => decide (x = x.reverse)) := by
  obtain ⟨L, hL, hpair⟩ := MPP.Solutions.Pnp085.main
  obtain ⟨h1⟩ := MPP.Solutions.Pnp090.main
  obtain ⟨h2⟩ := hL
  obtain ⟨h3⟩ := MPP.Solutions.Pnp006.main h1 h2
  have hfun : (L ∘ fun x : List Bool => pair x x.reverse) =
      fun x : List Bool => decide (x = x.reverse) := by
    funext x
    simp only [Function.comp_apply]
    rw [hpair]
    exact decide_eq_decide.mpr eq_comm
  rw [hfun] at h3
  exact ⟨h3⟩

end MPP.Solutions.Pnp089
