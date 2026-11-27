import Mathlib
import MPP.Solutions.Pnp266

namespace MPP.Solutions.Pnp267

theorem main : ∀ (items : List (List (Bool × Bool))) (T : List (Bool × Bool)),
    (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0) →
    (∀ j, j ≤ T.length →
      0 ≤ ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    -(items.length : ℤ) ≤
      ((((items.map fun b => b ++ [(true, true)]).flatten ++ T).map fun r : Bool × Bool =>
        if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum) := by
  intro items T hyp htail
  have h := MPP.Solutions.Pnp266.main items T hyp
  have hT := htail T.length le_rfl
  rw [List.take_of_length_le (by simp)] at hT
  rw [h]
  linarith

end MPP.Solutions.Pnp267
