import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp011
import MPP.Solutions.Pnp050

namespace MPP.Solutions.Pnp049

open MPP.PvsNP Turing

theorem main : ∀ L : Lang, (∃ V : Lang, InP V ∧ ∃ p : Polynomial ℕ, ∀ x : List Bool,
    (L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true)) → InNP L := by
  rintro L ⟨V, hV, p, hp⟩
  obtain ⟨E, hE, hEx⟩ := MPP.Solutions.Pnp050.main p
  refine ⟨fun y => E y && V y, MPP.Solutions.Pnp011.main E V hE hV, p, fun x => ?_⟩
  constructor
  · intro hL
    obtain ⟨w, hw, hVw⟩ := (hp x).1 hL
    refine ⟨w, le_of_eq hw, ?_⟩
    dsimp only
    rw [Bool.and_eq_true]
    exact ⟨(hEx x w).2 hw, hVw⟩
  · rintro ⟨w, _, hw'⟩
    dsimp only at hw'
    rw [Bool.and_eq_true] at hw'
    exact (hp x).2 ⟨w, (hEx x w).1 hw'.1, hw'.2⟩

end MPP.Solutions.Pnp049
