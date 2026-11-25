import Mathlib

namespace MPP.Solutions.Pnp156

/-- Strong form by length: peel off two bits at a time from the front. -/
theorem split_le (n : ℕ) : ∀ x : List Bool, x.length ≤ n →
    ∃ (ps : List (Bool × Bool)) (r : List Bool),
      x = ps.flatMap (fun q => [q.1, q.2]) ++ r ∧ r.length ≤ 1 := by
  induction n with
  | zero =>
    intro x hx
    have hx0 : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx0
    exact ⟨[], [], by simp, by simp⟩
  | succ n ih =>
    intro x hx
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact ⟨[], [], by simp, by simp⟩
    · exact ⟨[], [a], by simp, by simp⟩
    · simp only [List.length_cons] at hx
      obtain ⟨ps, r, h1, h2⟩ := ih rest (by omega)
      refine ⟨(a, b) :: ps, r, ?_, h2⟩
      rw [h1]
      simp [List.append_assoc]

theorem main : ∀ x : List Bool, ∃ (ps : List (Bool × Bool)) (r : List Bool),
    x = ps.flatMap (fun q => [q.1, q.2]) ++ r ∧ r.length ≤ 1 :=
  fun x => split_le x.length x le_rfl

end MPP.Solutions.Pnp156
