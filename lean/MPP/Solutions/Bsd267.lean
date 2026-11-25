import Mathlib

namespace MPP.Solutions.Bsd267

theorem main : ∀ (A : Type) [CommRing A] (b c d : A),
    normEDS b c d (2 + 4) * normEDS b c d (2 - 4)
      - normEDS b c d 4 ^ 2 * normEDS b c d (2 + 1) * normEDS b c d (2 - 1)
      + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d 2 ^ 2 = 0 := by
  intro A _ b c d
  have h6 := normEDS_even b c d 3
  norm_num at h6 ⊢
  linear_combination (-1 : A) * h6

end MPP.Solutions.Bsd267
