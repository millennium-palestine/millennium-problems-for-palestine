import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp079

namespace MPP.Solutions.Pnp080

open MPP.PvsNP Turing

theorem main : ∀ (V : Lang) (p : Polynomial ℕ), InP V → PEqualsNP →
    ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x : List Bool, (∃ w : List Bool, w.length ≤ p.eval x.length ∧ V (pair x w) = true) →
        (f x).length ≤ p.eval x.length ∧ V (pair x (f x)) = true := by
  intro V p hV hPNP
  obtain ⟨f, hf, hfx⟩ := MPP.Solutions.Pnp079.main V p hV hPNP
  exact ⟨f, hf, fun x hw => ⟨(hfx x hw).1, (hfx x hw).2.1⟩⟩

end MPP.Solutions.Pnp080
