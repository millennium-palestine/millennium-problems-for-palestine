import Mathlib

namespace MPP.Solutions.Bsd013

theorem main : ∀ x y : ℚ, y ^ 2 = x ^ 3 - x → y = 0 → x = 0 ∨ x = 1 ∨ x = -1 := by
  intro x y hxy hy
  subst hy
  have h : x * ((x - 1) * (x + 1)) = 0 := by
    have h0 : x ^ 3 - x = 0 := by
      have := hxy
      simp at this
      linarith
    linear_combination h0
  rcases mul_eq_zero.mp h with h1 | h1
  · exact Or.inl h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

end MPP.Solutions.Bsd013
