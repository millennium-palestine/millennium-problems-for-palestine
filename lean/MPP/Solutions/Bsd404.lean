import Mathlib

namespace MPP.Solutions.Bsd404

theorem main : ∀ (R : Type) [CommRing R] (c : R →+* R) (π : R) (a p m n : ℤ),
    π + c π = (a : R) → π * c π = (p : R) →
      ((m : R) - (n : R) * π) * ((m : R) - (n : R) * c π) =
        (m : R) ^ 2 - (a : R) * (m : R) * (n : R) + (p : R) * (n : R) ^ 2 := by
  intro R _ c π a p m n h1 h2
  linear_combination (-(m : R) * (n : R)) * h1 + (n : R) ^ 2 * h2

end MPP.Solutions.Bsd404
