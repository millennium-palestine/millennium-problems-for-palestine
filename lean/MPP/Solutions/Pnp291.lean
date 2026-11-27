import Mathlib

namespace MPP.Solutions.Pnp291

theorem main : ∀ n t : ℕ, t < n * (n + 1) / 2 → ∃ j i : ℕ, i ≤ j ∧ j < n ∧ j * (j + 1) / 2 + i = t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    simp at ht
  | succ n ih =>
    intro t ht
    have h1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
    have key : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
      rw [h1]
      exact Nat.add_mul_div_left (n * (n + 1)) (n + 1) (by norm_num)
    rw [key] at ht
    by_cases h : t < n * (n + 1) / 2
    · obtain ⟨j, i, hij, hjn, heq⟩ := ih t h
      exact ⟨j, i, hij, by omega, heq⟩
    · refine ⟨n, t - n * (n + 1) / 2, ?_, by omega, ?_⟩
      · omega
      · omega

end MPP.Solutions.Pnp291
