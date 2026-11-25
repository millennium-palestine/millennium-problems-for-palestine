import Mathlib

namespace MPP.Solutions.Bsd175

theorem main : ∀ (a p : ℤ) (c : ℕ → ℤ), c 0 = 1 → c 1 = a →
    (∀ k : ℕ, c (k + 2) = a * c (k + 1) - p * c k) →
    ∀ k : ℕ, c (k + 1) ^ 2 - a * c k * c (k + 1) + p * c k ^ 2 = p ^ (k + 1) := by
  intro a p c h0 h1 h k
  induction k with
  | zero => simp only [h0, h1]; ring
  | succ n ih =>
    have := h n
    calc c (n + 1 + 1) ^ 2 - a * c (n + 1) * c (n + 1 + 1) + p * c (n + 1) ^ 2
        = p * (c (n + 1) ^ 2 - a * c n * c (n + 1) + p * c n ^ 2) := by
          rw [show n + 1 + 1 = n + 2 from rfl, this]; ring
      _ = p ^ (n + 1 + 1) := by rw [ih]; ring

end MPP.Solutions.Bsd175
