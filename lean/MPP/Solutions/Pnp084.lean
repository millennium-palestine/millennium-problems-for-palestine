import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp044
import MPP.Solutions.Pnp083

namespace MPP.Solutions.Pnp084

open Turing MPP.PvsNP

theorem main : PEqualsNP → ∀ L : Lang, InNP L →
    ∃ (V : Lang) (p : Polynomial ℕ), InP V ∧
      (∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) ∧
      ∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ x : List Bool, L x = true →
          (f x).length = p.eval x.length ∧ V (pair x (f x)) = true ∧
          ∀ w : List Bool, w.length = p.eval x.length → V (pair x w) = true → ¬ (f x < w) := by
  intro hP L hL
  obtain ⟨V, hV, p, hLV⟩ := MPP.Solutions.Pnp044.main L hL
  obtain ⟨f, hf, hfp⟩ := MPP.Solutions.Pnp083.main V p hV hP
  exact ⟨V, p, hV, hLV, f, hf, fun x hx => hfp x ((hLV x).mp hx)⟩

end MPP.Solutions.Pnp084
