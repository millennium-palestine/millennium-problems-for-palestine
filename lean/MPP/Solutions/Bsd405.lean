import Mathlib

namespace MPP.Solutions.Bsd405

theorem main : ∀ (R : Type) [CommRing R] (c : R →+* R) (π : R) (a p : ℤ),
    π + c π = (a : R) → π * c π = (p : R) →
      π ^ 2 - (a : R) * π + (p : R) = 0 := by
  intro R _ c π a p h1 h2
  linear_combination π * h1 - h2

end MPP.Solutions.Bsd405
