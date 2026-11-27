import Mathlib

namespace MPP.Solutions.Pnp304

theorem main : ∀ (n : ℕ) (x : Fin n → Bool), ∃ D : List (List (ℕ × Bool)),
    (∀ a : ℕ → Bool, (∀ i : Fin n, a i.val = x i) ↔ ∀ d ∈ D, ∃ l ∈ d, a l.1 = l.2) ∧
    D.length ≤ n ∧ ∀ d ∈ D, ∀ l ∈ d, l.1 < n := by
  intro n x
  refine ⟨(List.finRange n).map (fun i => [(i.val, x i)]), ?_, ?_, ?_⟩
  · intro a
    simp [List.mem_map, List.mem_finRange]
  · simp
  · intro d hd l hl
    simp only [List.mem_map, List.mem_finRange, true_and] at hd
    obtain ⟨i, rfl⟩ := hd
    simp only [List.mem_singleton] at hl
    subst hl
    exact i.isLt

end MPP.Solutions.Pnp304
