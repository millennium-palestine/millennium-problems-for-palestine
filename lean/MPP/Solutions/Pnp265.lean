import Mathlib

namespace MPP.Solutions.Pnp265

theorem main : ∀ items : List (List (Bool × Bool)),
    (∀ b ∈ items, (b.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0) →
    ((((items.map fun b => b ++ [(true, true)]).flatten).map fun r : Bool × Bool =>
      if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum) = -(items.length : ℤ) := by
  intro items
  induction items with
  | nil =>
    intro _
    simp
  | cons b rest ih =>
    intro hyp
    have hb := hyp b (by simp)
    have hrest := ih (fun c hc => hyp c (by simp [hc]))
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.sum_append, List.length_cons]
    simp only [List.map_flatten, List.map_map, Function.comp_def] at hrest ⊢
    rw [hb, hrest]
    simp

end MPP.Solutions.Pnp265
