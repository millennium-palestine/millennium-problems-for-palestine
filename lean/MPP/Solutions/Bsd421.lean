import Mathlib

namespace MPP.Solutions.Bsd421

theorem main : ∀ (K : Type) [Field K] (f : Polynomial K),
    IsCoprime f (Polynomial.derivative f) → Squarefree f := by
  intro K _ f h
  exact Polynomial.Separable.squarefree (show f.Separable from h)

end MPP.Solutions.Bsd421
