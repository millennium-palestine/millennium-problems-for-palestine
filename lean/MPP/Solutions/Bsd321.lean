import Mathlib

namespace MPP.Solutions.Bsd321

theorem main : ∀ (A : Type) [CommRing A] (b c d : A),
    normEDS b c d (2 + 5) * normEDS b c d (2 - 5)
      - normEDS b c d (2 + 1) * normEDS b c d (2 - 1) * normEDS b c d 5 ^ 2
      + normEDS b c d 6 * normEDS b c d 4 * normEDS b c d 2 ^ 2 = 0 := by
  intro A _ b c d
  have h5 : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
    have h := normEDS_odd b c d 2
    norm_num at h
    rw [h]
    ring
  have h6 : normEDS b c d 6 * b = b ^ 2 * c * (normEDS b c d 5 - d ^ 2) := by
    have h := normEDS_even b c d 3
    norm_num at h
    linear_combination h
  have h7 : normEDS b c d 7 = normEDS b c d 5 * c ^ 3 - b * (d * b) ^ 3 := by
    have h := normEDS_odd b c d 3
    norm_num at h
    linear_combination h
  have hm3 : normEDS b c d (-3) = -c := by
    rw [normEDS_neg, normEDS_three]
  rw [show (2 : ℤ) + 5 = 7 by norm_num, show (2 : ℤ) - 5 = -3 by norm_num,
    show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, hm3,
    normEDS_three, normEDS_one, normEDS_four, normEDS_two]
  linear_combination (-c) * h7 + (d * b ^ 2) * h6 + (-c * normEDS b c d 5) * h5

end MPP.Solutions.Bsd321
