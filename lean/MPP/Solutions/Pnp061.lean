import Mathlib
import MPP.Solutions.Pnp066
import MPP.Solutions.Pnp067

namespace MPP.Solutions.Pnp061

open Turing

theorem main : ∀ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ z : List Bool, (s z).length = z.length + 1) →
    ∀ p : Polynomial ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, T z = s^[p.eval z.length] z :=
  MPP.Solutions.Pnp067.main MPP.Solutions.Pnp066.main

end MPP.Solutions.Pnp061
