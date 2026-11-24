import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp044
import MPP.Solutions.Pnp072

namespace MPP.Solutions.Pnp078

open MPP.PvsNP Turing

theorem main : PEqualsNP → ∀ L : Lang, InNP L →
    ∃ (V : Lang) (p : Polynomial ℕ), InP V ∧
      (∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) ∧
      ∃ f : List Bool → List Bool,
        Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
        ∀ x : List Bool, L x = true →
          (f x).length = p.eval x.length ∧ V (pair x (f x)) = true ∧
          ∀ w : List Bool, w.length = p.eval x.length → V (pair x w) = true → ¬ (w < f x) := by
  intro hP L hL
  obtain ⟨V, hV, p, hLV⟩ := MPP.Solutions.Pnp044.main L hL
  obtain ⟨f, hf, hmin⟩ := MPP.Solutions.Pnp072.main V p hV hP
  exact ⟨V, p, hV, hLV, f, hf, fun x hx => hmin x ((hLV x).1 hx)⟩

end MPP.Solutions.Pnp078
