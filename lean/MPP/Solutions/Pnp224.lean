import Mathlib
import MPP.Solutions.Pnp214

namespace MPP.Solutions.Pnp224

open Turing

theorem main : ∀ (s : List Bool → List Bool),
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ z : List Bool, (s z).length = z.length) →
    ∀ p : Polynomial ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, T z = s^[p.eval z.length] z := by
  intro s hs hlen p
  exact MPP.Solutions.Pnp214.main s 0 hs (fun z => by simp [hlen z]) p

end MPP.Solutions.Pnp224
