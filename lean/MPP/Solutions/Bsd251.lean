import Mathlib

namespace MPP.Solutions.Bsd251

theorem main : ∀ (R : Type) [CommRing R] (π π' : R) (a p m n : ℤ),
    π + π' = (a : R) → π * π' = (p : R) →
    ((m : R) - (n : R) * π) * ((m : R) - (n : R) * π') =
      (m : R) ^ 2 - (a : R) * (m : R) * (n : R) + (p : R) * (n : R) ^ 2 := by
  intro R _ π π' a p m n hsum hprod
  linear_combination (-(m : R) * (n : R)) * hsum + (n : R) ^ 2 * hprod

end MPP.Solutions.Bsd251
