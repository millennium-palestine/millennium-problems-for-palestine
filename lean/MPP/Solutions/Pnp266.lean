import Mathlib
import MPP.Solutions.Pnp265

namespace MPP.Solutions.Pnp266

theorem main : ∀ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
    (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0) →
    ((((items.map fun b => b ++ [(true, true)]).flatten ++ T).map fun r : Bool × Bool =>
      if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum) =
      -(items.length : ℤ) + (T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum := by
  intro items T hyp
  rw [List.map_append, List.sum_append, MPP.Solutions.Pnp265.main items hyp]

end MPP.Solutions.Pnp266
