import Mathlib

namespace MPP.Solutions.Pnp309

theorem main : ∀ (k : ℕ) (b : Bool) (a : ℕ → Bool),
    (∀ c ∈ [[(k, b)]], ∃ l ∈ c, a l.1 = l.2) ↔ a k = b := by
  intro k b a
  simp

end MPP.Solutions.Pnp309
