import Mathlib

namespace MPP.Solutions.Bsd266

-- The telescoping identity for the n = 4 bracket, written for an arbitrary function of atoms X k.
theorem telescope_atoms (A : Type) [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, -2 ≤ j → j ≤ 2 →
      X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, -2 ≤ j → j ≤ 2 →
      X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0) :
    X (-1) * X 0 * X 1 *
        (X 5 * X (-3) - (d * b) ^ 2 * X 2 * X 0 + (d * b ^ 4 - c ^ 3) * c * X 1 ^ 2) =
      X 0 * X 1 * X 2 *
        (X 4 * X (-4) - (d * b) ^ 2 * X 1 * X (-1) + (d * b ^ 4 - c ^ 3) * c * X 0 ^ 2) := by
  have a2m2 := h2 (-2) (by norm_num) (by norm_num)
  have a2m1 := h2 (-1) (by norm_num) (by norm_num)
  have a2_0 := h2 0 (by norm_num) (by norm_num)
  have a2_1 := h2 1 (by norm_num) (by norm_num)
  have a2_2 := h2 2 (by norm_num) (by norm_num)
  have a3_0 := h3 0 (by norm_num) (by norm_num)
  have a3_1 := h3 1 (by norm_num) (by norm_num)
  have a3_2 := h3 2 (by norm_num) (by norm_num)
  norm_num at a2m2 a2m1 a2_0 a2_1 a2_2 a3_0 a3_1 a3_2
  linear_combination (-(X 1 * X 2 * X 4)) * a2m2
    + (X (-1) * X 0 * X 5 + X (-1) * X 2 * X 3 * d - X 0 * X 1 * X 3 * c ^ 2 + X 1 * X 2 ^ 2 * b ^ 2 * d) * a2m1
    + (X (-3) * X 2 * X 4 + X (-2) * X 1 * X 4 * c + X (-1) * X 0 * X 3 * b ^ 2 * d
        - X (-1) * X 0 * X 4 * d - X 0 ^ 2 * X 2 * b ^ 4 * d + X 0 * X 1 * X 2 * b ^ 4 * d) * a2_0
    + (-(X (-1) * X 1 * X 2 * d) + X 0 * X 1 ^ 2 * c ^ 2 - X 0 * X 1 * X 2 * b ^ 2 * c) * a3_0
    + (-(X (-1) ^ 2 * X 2 * c * d) + X (-1) * X 0 * X 1 * b ^ 4 * d - X (-1) * X 1 ^ 2 * b ^ 4 * d
        - X 0 ^ 3 * b ^ 2 * c * d + X 0 ^ 2 * X 1 * b ^ 2 * c * d) * a2_1
    + (-(X (-3) * X 2 ^ 2) + X (-1) * X 0 * X 2 * d + X (-1) * X 1 ^ 2 * b ^ 2 * c - X 0 ^ 2 * X 1 * c ^ 2) * a3_1
    + (-(X (-3) * X 0 * X 2 * c) - X (-1) ^ 2 * X 1 * b ^ 2 * d + X (-1) * X 0 ^ 2 * c * d) * a2_2
    + (X (-2) * X 0 ^ 2 * b ^ 2 - X (-1) ^ 2 * X 0 * c) * a3_2

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    (∀ k : ℤ, m - 2 ≤ k → k ≤ m + 2 →
      normEDS b c d (k + 2) * normEDS b c d (k - 2) - b ^ 2 * normEDS b c d (k + 1) * normEDS b c d (k - 1)
        + c * normEDS b c d k ^ 2 = 0) →
    (∀ k : ℤ, m - 2 ≤ k → k ≤ m + 2 →
      normEDS b c d (k + 3) * normEDS b c d (k - 3) - c ^ 2 * normEDS b c d (k + 1) * normEDS b c d (k - 1)
        + normEDS b c d 4 * b * normEDS b c d k ^ 2 = 0) →
    normEDS b c d (m - 1) * normEDS b c d m * normEDS b c d (m + 1) *
        (normEDS b c d (m + 1 + 4) * normEDS b c d (m + 1 - 4)
          - normEDS b c d 4 ^ 2 * normEDS b c d (m + 1 + 1) * normEDS b c d (m + 1 - 1)
          + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d (m + 1) ^ 2) =
      normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m + 2) *
        (normEDS b c d (m + 4) * normEDS b c d (m - 4)
          - normEDS b c d 4 ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
          + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d m ^ 2) := by
  intro A _ b c d m h2 h3
  have e4 : normEDS b c d 4 = d * b := normEDS_four b c d
  have e3 : normEDS b c d 3 = c := normEDS_three b c d
  have e5 : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
    have h := normEDS_odd b c d 2
    norm_num at h
    rw [h]
    ring
  rw [e4, e5, e3]
  have key := telescope_atoms A b c d (fun k => normEDS b c d (m + k))
    (fun j hj1 hj2 => by
      have h := h2 (m + j) (by omega) (by omega)
      simpa only [add_assoc, add_sub_assoc] using h)
    (fun j hj1 hj2 => by
      have h := h3 (m + j) (by omega) (by omega)
      rw [e4] at h
      simpa only [add_assoc, add_sub_assoc] using h)
  ring_nf at key ⊢
  linear_combination key

end MPP.Solutions.Bsd266
