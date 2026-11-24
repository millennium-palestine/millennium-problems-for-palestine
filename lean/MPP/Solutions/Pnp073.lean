import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp069

namespace MPP.Solutions.Pnp073

open MPP.PvsNP Turing

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V →
    (¬ ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
        (f x).length = p.eval x.length ∧ V (pair x (f x)) = true) →
    ¬ PEqualsNP := by
  intro V p hV hno hPNP
  exact hno (MPP.Solutions.Pnp069.main V p hV hPNP)

end MPP.Solutions.Pnp073
