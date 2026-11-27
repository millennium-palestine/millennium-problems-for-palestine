import Mathlib

namespace MPP.Solutions.Pnp300

theorem main : ∀ (C : List (List (ℕ × Bool))) (w : List Bool),
    (∀ c ∈ C, ∃ l ∈ c, w.getD l.1 false = l.2) ↔
      C.all (fun c => c.any (fun l => (w.getD l.1 false == l.2))) = true := by
  intro C w
  simp [List.all_eq_true, List.any_eq_true]

end MPP.Solutions.Pnp300
