import Mathlib

namespace MPP.Solutions.Bsd153

theorem main : ∀ (R : Type) [CommRing R] (π : R) (a p m n : ℤ),
    π * π - (a : R) * π + (p : R) = 0 →
      ((m : R) - (n : R) * π) * ((m : R) - (n : R) * ((a : R) - π)) =
        (m : R) ^ 2 - (a : R) * (m : R) * (n : R) + (p : R) * (n : R) ^ 2 := by
  intro R _ π a p m n h
  linear_combination (-(n : R) ^ 2) * h

end MPP.Solutions.Bsd153
