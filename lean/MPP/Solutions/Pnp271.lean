import Mathlib

namespace MPP.Solutions.Pnp271

theorem main : ∀ x : List Bool, ∃ (q : List (Bool × Bool)) (o : List Bool), x = q.flatMap (fun r : Bool × Bool => [r.1, r.2]) ++ o ∧ o.length ≤ 1 := by
  suffices H : ∀ n : ℕ, ∀ x : List Bool, x.length ≤ n → ∃ (q : List (Bool × Bool)) (o : List Bool), x = q.flatMap (fun r : Bool × Bool => [r.1, r.2]) ++ o ∧ o.length ≤ 1 from
    fun x => H x.length x le_rfl
  intro n
  induction n with
  | zero =>
    intro x hx
    have hnil : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], [], by simp [hnil], by simp⟩
  | succ n ih =>
    intro x hx
    match x, hx with
    | [], _ => exact ⟨[], [], by simp, by simp⟩
    | [a], _ => exact ⟨[], [a], by simp, by simp⟩
    | a :: b :: rest, hx =>
      obtain ⟨q, o, h1, h2⟩ := ih rest (by simp at hx; omega)
      refine ⟨(a, b) :: q, o, ?_, h2⟩
      rw [h1]
      simp

end MPP.Solutions.Pnp271
