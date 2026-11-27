import Mathlib

namespace MPP.Solutions.Pnp308

theorem main : ∀ (C D : List (List (ℕ × Bool))) (a : ℕ → Bool),
    (∀ c ∈ C ++ D, ∃ l ∈ c, a l.1 = l.2) ↔
      (∀ c ∈ C, ∃ l ∈ c, a l.1 = l.2) ∧ (∀ c ∈ D, ∃ l ∈ c, a l.1 = l.2) := by
  intro C D a
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left D hc),
      fun c hc => h c (List.mem_append_right C hc)⟩
  · rintro ⟨h1, h2⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

end MPP.Solutions.Pnp308
