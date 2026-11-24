import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp073
import MPP.Solutions.Pnp074

namespace MPP.Solutions.Pnp075

open MPP.PvsNP Turing

theorem main : ¬ PEqualsNP ↔ ∃ (V : Lang) (p : Polynomial ℕ), InP V ∧
    ¬ ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length = p.eval x.length ∧ V (pair x w) = true) →
        (f x).length = p.eval x.length ∧ V (pair x (f x)) = true := by
  constructor
  · intro hne
    by_contra hcon
    apply hne
    apply MPP.Solutions.Pnp074.main
    intro V p hV
    by_contra hf
    exact hcon ⟨V, p, hV, hf⟩
  · rintro ⟨V, p, hV, hno⟩
    exact MPP.Solutions.Pnp073.main V p hV hno

end MPP.Solutions.Pnp075
