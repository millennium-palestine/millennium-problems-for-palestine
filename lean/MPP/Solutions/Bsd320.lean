import Mathlib
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd322
import MPP.Solutions.Bsd323
import MPP.Solutions.Bsd324
import MPP.Solutions.Bsd325

namespace MPP.Solutions.Bsd320

/-! The n = 5 elliptic-net relation `N(m+5) N(m-5) - N(m+1) N(m-1) N(5)^2 + N(6) N(4) N(m)^2 = 0`
for `normEDS`, in an arbitrary commutative ring.

In the universal domain `R` with `b ≠ 0` and `normEDS` nonzero off zero, the bracket times
`N(m-4) N(m-3)` vanishes by the certificate of bsd-322, so the bracket vanishes for m ∉ {3, 4}.
For m ∈ {3, 4} a second certificate (`cert12` below, with the atoms `X 1` and `X 2`, using only the
n = 2 and n = 3 relations) gives the bracket times `N(m+1) N(m+2)`, which vanishes. The relations
at all indices come from bsd-323, bsd-324 and bsd-325. The result is transferred to `A` by the
evaluation at `![b, c, d]`. -/

lemma cert12 {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
  (h2 : ∀ j : ℤ, -1 ≤ j → j ≤ 3 →
      X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
  (h3 : ∀ j : ℤ, -2 ≤ j → j ≤ 2 →
      X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0) :
  X 1 * X 2 * (X 5 * X (-5) - (d * b ^ 4 - c ^ 3) ^ 2 * X 1 * X (-1) + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X 0 ^ 2) = 0 := by
  have e2m1 := h2 (-1) (by norm_num) (by norm_num)
  have e20 := h2 (0) (by norm_num) (by norm_num)
  have e21 := h2 (1) (by norm_num) (by norm_num)
  have e22 := h2 (2) (by norm_num) (by norm_num)
  have e23 := h2 (3) (by norm_num) (by norm_num)
  have e3m2 := h3 (-2) (by norm_num) (by norm_num)
  have e30 := h3 (0) (by norm_num) (by norm_num)
  have e31 := h3 (1) (by norm_num) (by norm_num)
  have e32 := h3 (2) (by norm_num) (by norm_num)
  norm_num at e2m1 e20 e21 e22 e23 e3m2 e30 e31 e32
  linear_combination -(c ^ 1 * d ^ 1) * (X (0) * X (5)) * e2m1
    + (2) * (c ^ 2 * d ^ 1) * (X (1) * X (4)) * e2m1
    + -(b ^ 4 * c ^ 1 * d ^ 1) * (X (2) * X (3)) * e2m1
    + (c ^ 1 * d ^ 2) * (X (2) * X (3)) * e2m1
    + -(b ^ 2 * d ^ 1) * (X (-2) * X (5)) * e20
    + (b ^ 2 * c ^ 1 * d ^ 2) * (X (0) * X (3)) * e20
    + -(b ^ 2 * c ^ 3 * d ^ 1) * (X (1) * X (2)) * e20
    + (-2) * (c ^ 1 * d ^ 1) * (X (-3) * X (4)) * e21
    + (b ^ 4 * c ^ 1 * d ^ 1) * (X (-2) * X (3)) * e21
    + (b ^ 4 * c ^ 2 * d ^ 1) * (X (-1) * X (2)) * e21
    + -(c ^ 2 * d ^ 2) * (X (-1) * X (2)) * e21
    + -(b ^ 4 * c ^ 1 * d ^ 2) * (X (0) * X (1)) * e21
    + -(b ^ 2 * c ^ 1 * d ^ 1) * (X (-3) * X (2)) * e22
    + (b ^ 2 * c ^ 2 * d ^ 1) * (X (-2) * X (1)) * e22
    + (-2) * (b ^ 2 * c ^ 1 * d ^ 2) * (X (-1) * X (0)) * e22
    + (c ^ 1 * d ^ 1) * (X (-3) * X (0)) * e23
    + -(b ^ 4 * d ^ 1) * (X (-2) * X (-1)) * e23
    + (1) * (X (2) * X (5)) * e3m2
    + (2) * (c ^ 1 * d ^ 1) * (X (-1) * X (4)) * e30
    + -(c ^ 2 * d ^ 1) * (X (0) * X (3)) * e30
    + (c ^ 4) * (X (1) * X (2)) * e30
    + -(c ^ 1 * d ^ 2) * (X (1) * X (2)) * e30
    + -(b ^ 6 * d ^ 1) * (X (-1) * X (2)) * e31
    + (b ^ 2 * c ^ 2 * d ^ 1) * (X (0) * X (1)) * e31
    + (c ^ 2) * (X (-3) * X (2)) * e32
    + (c ^ 2 * d ^ 1) * (X (-1) * X (0)) * e32


section Gen

variable {R : Type} [CommRing R] [IsDomain R] (b c d : R)

omit [IsDomain R] in
lemma n5 : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
  have h := normEDS_odd b c d 2
  norm_num at h
  rw [h]
  ring

lemma n6 (hb : b ≠ 0) : normEDS b c d 6 = b * c * (normEDS b c d 5 - d ^ 2) := by
  have h := normEDS_even b c d 3
  norm_num at h
  apply mul_right_cancel₀ hb
  linear_combination h

omit [IsDomain R] in
lemma rel2 (m j : ℤ) :
    normEDS b c d (m + (j + 2)) * normEDS b c d (m + (j - 2))
      - b ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + c * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd323.main R b c d (m + j)
  rw [show m + j + 2 = m + (j + 2) by ring, show m + j - 2 = m + (j - 2) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring] at h
  exact h

omit [IsDomain R] in
lemma rel3 (m j : ℤ) :
    normEDS b c d (m + (j + 3)) * normEDS b c d (m + (j - 3))
      - c ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + d * b * b * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd324.main R b c d (m + j)
  rw [show m + j + 3 = m + (j + 3) by ring, show m + j - 3 = m + (j - 3) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    normEDS_four] at h
  linear_combination h

omit [IsDomain R] in
lemma rel4 (m j : ℤ) :
    normEDS b c d (m + (j + 4)) * normEDS b c d (m + (j - 4))
      - (d * b) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + (d * b ^ 4 - c ^ 3) * c * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd325.main R b c d (m + j)
  rw [show m + j + 4 = m + (j + 4) by ring, show m + j - 4 = m + (j - 4) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    normEDS_four, n5 b c d, normEDS_three] at h
  linear_combination h

lemma gen (hb : b ≠ 0) (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (m : ℤ) :
    normEDS b c d (m + 5) * normEDS b c d (m - 5)
      - normEDS b c d 5 ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + normEDS b c d 6 * normEDS b c d 4 * normEDS b c d m ^ 2 = 0 := by
  have hpoly : normEDS b c d (m + 5) * normEDS b c d (m - 5)
      - (d * b ^ 4 - c ^ 3) ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * normEDS b c d m ^ 2 = 0 := by
    by_cases hm : m = 3 ∨ m = 4
    · have h := cert12 b c d (fun k => normEDS b c d (m + k))
        (fun j _ _ => rel2 b c d m j) (fun j _ _ => rel3 b c d m j)
      rw [add_zero, show m + -5 = m - 5 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m + 1) * normEDS b c d (m + 2) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
    · have h := MPP.Solutions.Bsd322.main R b c d (fun k => normEDS b c d (m + k))
        (fun j _ _ => rel2 b c d m j) (fun j _ _ => rel3 b c d m j)
        (fun j _ _ => rel4 b c d m j)
      rw [add_zero, show m + -4 = m - 4 by ring, show m + -3 = m - 3 by ring,
        show m + -5 = m - 5 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m - 4) * normEDS b c d (m - 3) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
  rw [n6 b c d hb, normEDS_four, n5 b c d]
  linear_combination hpoly

end Gen

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 5) * normEDS b c d (m - 5)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 5 ^ 2
      + normEDS b c d 6 * normEDS b c d 4 * normEDS b c d m ^ 2 = 0 := by
  intro A _ b c d m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hu := gen (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1)
    (MvPolynomial.X 2) hb (fun k hk => MPP.Solutions.Bsd225.main k hk) m
  have hf := congrArg (MvPolynomial.aeval ![b, c, d] :
    MvPolynomial (Fin 3) ℤ →ₐ[ℤ] A) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  linear_combination hf

end MPP.Solutions.Bsd320
