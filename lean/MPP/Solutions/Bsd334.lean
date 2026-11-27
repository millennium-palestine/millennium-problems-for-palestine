import Mathlib
import MPP.Solutions.Bsd335

namespace MPP.Solutions.Bsd334

/-! The n = 7 elliptic-net relation for `normEDS` is the lemma `N7.main` of bsd-335, which proves it
in an arbitrary commutative ring by the same certificates as bsd-328 and bsd-335 (relations of n = 2..6,
evaluation from the universal domain `MvPolynomial (Fin 3) ℤ`). -/

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 7) * normEDS b c d (m - 7)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 7 ^ 2
      + normEDS b c d 8 * normEDS b c d 6 * normEDS b c d m ^ 2 = 0 :=
  MPP.Solutions.Bsd335.N7.main

end MPP.Solutions.Bsd334
