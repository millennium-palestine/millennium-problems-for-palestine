import Mathlib

namespace MPP.Solutions.Bsd290

theorem main : ∀ (R : Type) [CommRing R] (π σ : R) (a p m n : ℤ),
    π + σ = (a : R) → π * σ = (p : R) →
    ((m : R) - (n : R) * π) * ((m : R) - (n : R) * σ) = ((m ^ 2 - a * m * n + p * n ^ 2 : ℤ) : R) := by
  intro R _ π σ a p m n h1 h2
  push_cast
  linear_combination (-((m : R) * (n : R))) * h1 + ((n : R) ^ 2) * h2

end MPP.Solutions.Bsd290
