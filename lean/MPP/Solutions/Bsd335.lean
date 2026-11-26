import Mathlib
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd320
import MPP.Solutions.Bsd323
import MPP.Solutions.Bsd324
import MPP.Solutions.Bsd325
import MPP.Solutions.Bsd328

namespace MPP.Solutions.Bsd335

/-! The n = 8 elliptic-net relation `N(m+8) N(m-8) - N(m+1) N(m-1) N(8)^2 + N(9) N(7) N(m)^2 = 0`
for `normEDS`, in an arbitrary commutative ring.

Uses the relations of n = 2..7 (bsd-323, bsd-324, bsd-325, bsd-320, bsd-328, bsd-334) at shifted indices. Two
certificates express the bracket times `N(m-4) N(m-3)` (resp. `N(m+1) N(m+2)`) as a combination of those
relations, an exact identity in `Z[b, c, d]`. The bracket is then zero in the universal domain
`MvPolynomial (Fin 3) ℤ`, where normEDS is nonzero off zero (bsd-225), and the identity is transferred to `A`
by evaluation at `![b, c, d]`. -/

/-! The n = 7 relation, proved inline (bsd-334 is not yet on main), as in bsd-334. -/
namespace N7

/-! The n = 7 elliptic-net relation `N(m+7) N(m-7) - N(m+1) N(m-1) N(7)^2 + N(8) N(6) N(m)^2 = 0`
for `normEDS`, in an arbitrary commutative ring.

Uses the relations of n = 2..6 (bsd-323, bsd-324, bsd-325, bsd-320, bsd-328) at shifted indices. Two certificates
(`cert_a`, `cert_b`) express the bracket times `N(m-4) N(m-3)` (resp. `N(m+1) N(m+2)`) as a combination of
those relations, an exact identity in `Z[b, c, d]`. The bracket is then zero in the universal domain
`MvPolynomial (Fin 3) ℤ`, where normEDS is nonzero off zero (bsd-225), and the identity is transferred to `A`
by evaluation at `![b, c, d]`. -/

lemma cert_a {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - (d * b) ^ 2 * X (j + 1) * X (j - 1) + (d * b ^ 4 - c ^ 3) * c * X j ^ 2 = 0)
    (h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - (d * b ^ 4 - c ^ 3) ^ 2 * X (j + 1) * X (j - 1) + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X j ^ 2 = 0)
    (_h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * X j ^ 2 = 0) :
    X (-4) * X (-3) * (X 7 * X (-7)
      - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * X 1 * X (-1)
      + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X 0 ^ 2) = 0 := by
  have e2_m4 := h2 (-4)
  have e2_m3 := h2 (-3)
  have e2_m2 := h2 (-2)
  have e2_m1 := h2 (-1)
  have e2_0 := h2 0
  have e2_1 := h2 1
  have e3_m4 := h3 (-4)
  have e3_m3 := h3 (-3)
  have e3_m2 := h3 (-2)
  have e3_m1 := h3 (-1)
  have e3_0 := h3 0
  have e3_1 := h3 1
  have e4_m3 := h4 (-3)
  have e5_2 := h5 2
  norm_num at e2_m4 e2_m3 e2_m2 e2_m1 e2_0 e2_1 e3_m4 e3_m3 e3_m2 e3_m1 e3_0 e3_1 e4_m3 e5_2
  linear_combination
    -(b ^ 2 * c ^ 5 * d * X (-3) * X 4) * e2_m4
    + (-3) * (b ^ 2 * c ^ 8 * X (-2) * X 3) * e2_m4
    + (3) * (b ^ 6 * c ^ 5 * d * X (-2) * X 3) * e2_m4
    - (b ^ 10 * c ^ 2 * d ^ 2 * X (-2) * X 3) * e2_m4
    - (b ^ 2 * c ^ 5 * d ^ 2 * X (-2) * X 3) * e2_m4
    + (b ^ 6 * c ^ 2 * d ^ 3 * X (-2) * X 3) * e2_m4
    + (3) * (b ^ 2 * c ^ 9 * X (-1) * X 2) * e2_m4
    + (-3) * (b ^ 6 * c ^ 6 * d * X (-1) * X 2) * e2_m4
    + (b ^ 10 * c ^ 3 * d ^ 2 * X (-1) * X 2) * e2_m4
    + (2) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-1) * X 2) * e2_m4
    - (b ^ 6 * c ^ 3 * d ^ 3 * X (-1) * X 2) * e2_m4
    + (3) * (b ^ 6 * c ^ 8 * X 0 * X 1) * e2_m4
    + (-6) * (b ^ 10 * c ^ 5 * d * X 0 * X 1) * e2_m4
    + (4) * (b ^ 14 * c ^ 2 * d ^ 2 * X 0 * X 1) * e2_m4
    + (2) * (b ^ 6 * c ^ 5 * d ^ 2 * X 0 * X 1) * e2_m4
    + (-3) * (b ^ 10 * c ^ 2 * d ^ 3 * X 0 * X 1) * e2_m4
    - (b ^ 2 * c ^ 5 * d ^ 3 * X 0 * X 1) * e2_m4
    + (2) * (b ^ 6 * c ^ 2 * d ^ 4 * X 0 * X 1) * e2_m4
    - (c ^ 6 * d ^ 2 * X (-4) * X 3) * e2_m3
    + (b ^ 4 * c ^ 3 * d ^ 3 * X (-4) * X 3) * e2_m3
    - (b ^ 8 * d ^ 4 * X (-4) * X 3) * e2_m3
    + (-3) * (b ^ 8 * c ^ 6 * d * X (-3) * X 2) * e2_m3
    + (3) * (b ^ 12 * c ^ 3 * d ^ 2 * X (-3) * X 2) * e2_m3
    - (b ^ 4 * c ^ 6 * d ^ 2 * X (-3) * X 2) * e2_m3
    - (b ^ 16 * d ^ 3 * X (-3) * X 2) * e2_m3
    - (b ^ 8 * c ^ 3 * d ^ 3 * X (-3) * X 2) * e2_m3
    + (c ^ 6 * d ^ 3 * X (-3) * X 2) * e2_m3
    + (b ^ 12 * d ^ 4 * X (-3) * X 2) * e2_m3
    - (b ^ 4 * c ^ 3 * d ^ 4 * X (-3) * X 2) * e2_m3
    + (3) * (b ^ 4 * c ^ 10 * X (-2) * X 1) * e2_m3
    + (-3) * (b ^ 8 * c ^ 7 * d * X (-2) * X 1) * e2_m3
    + (b ^ 12 * c ^ 4 * d ^ 2 * X (-2) * X 1) * e2_m3
    + (2) * (b ^ 4 * c ^ 7 * d ^ 2 * X (-2) * X 1) * e2_m3
    - (b ^ 8 * c ^ 4 * d ^ 3 * X (-2) * X 1) * e2_m3
    - (c ^ 7 * d ^ 3 * X (-2) * X 1) * e2_m3
    + (2) * (b ^ 4 * c ^ 4 * d ^ 4 * X (-2) * X 1) * e2_m3
    - (b ^ 8 * c * d ^ 5 * X (-2) * X 1) * e2_m3
    + (-3) * (b ^ 8 * c ^ 6 * d ^ 2 * X (-1) * X 0) * e2_m3
    + (3) * (b ^ 12 * c ^ 3 * d ^ 3 * X (-1) * X 0) * e2_m3
    - (b ^ 4 * c ^ 6 * d ^ 3 * X (-1) * X 0) * e2_m3
    - (b ^ 16 * d ^ 4 * X (-1) * X 0) * e2_m3
    + (3) * (b ^ 2 * c ^ 7 * X (-6) * X 3) * e2_m2
    + (-3) * (b ^ 6 * c ^ 4 * d * X (-6) * X 3) * e2_m2
    + (b ^ 10 * c * d ^ 2 * X (-6) * X 3) * e2_m2
    + (b ^ 2 * c ^ 4 * d ^ 2 * X (-6) * X 3) * e2_m2
    - (b ^ 6 * c * d ^ 3 * X (-6) * X 3) * e2_m2
    + (-3) * (b ^ 2 * c ^ 9 * X (-5) * X 2) * e2_m2
    + (2) * (b ^ 10 * c ^ 3 * d ^ 2 * X (-5) * X 2) * e2_m2
    + (-2) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-5) * X 2) * e2_m2
    - (b ^ 14 * d ^ 3 * X (-5) * X 2) * e2_m2
    - (b ^ 6 * c ^ 3 * d ^ 3 * X (-5) * X 2) * e2_m2
    + (b ^ 10 * d ^ 4 * X (-5) * X 2) * e2_m2
    + (-3) * (b ^ 6 * c ^ 9 * X (-4) * X 1) * e2_m2
    + (6) * (b ^ 10 * c ^ 6 * d * X (-4) * X 1) * e2_m2
    + (-4) * (b ^ 14 * c ^ 3 * d ^ 2 * X (-4) * X 1) * e2_m2
    + (-2) * (b ^ 6 * c ^ 6 * d ^ 2 * X (-4) * X 1) * e2_m2
    + (3) * (b ^ 10 * c ^ 3 * d ^ 3 * X (-4) * X 1) * e2_m2
    + (b ^ 2 * c ^ 6 * d ^ 3 * X (-4) * X 1) * e2_m2
    + (-2) * (b ^ 6 * c ^ 3 * d ^ 4 * X (-4) * X 1) * e2_m2
    + (-3) * (b ^ 6 * c ^ 10 * X (-3) * X 0) * e2_m2
    + (6) * (b ^ 10 * c ^ 7 * d * X (-3) * X 0) * e2_m2
    + (-4) * (b ^ 14 * c ^ 4 * d ^ 2 * X (-3) * X 0) * e2_m2
    + (-5) * (b ^ 6 * c ^ 7 * d ^ 2 * X (-3) * X 0) * e2_m2
    + (6) * (b ^ 10 * c ^ 4 * d ^ 3 * X (-3) * X 0) * e2_m2
    + (b ^ 2 * c ^ 7 * d ^ 3 * X (-3) * X 0) * e2_m2
    - (b ^ 14 * c * d ^ 4 * X (-3) * X 0) * e2_m2
    + (-3) * (b ^ 6 * c ^ 4 * d ^ 4 * X (-3) * X 0) * e2_m2
    + (3) * (b ^ 6 * c ^ 9 * d * X (-2) * X (-1)) * e2_m2
    + (-6) * (b ^ 10 * c ^ 6 * d ^ 2 * X (-2) * X (-1)) * e2_m2
    + (4) * (b ^ 14 * c ^ 3 * d ^ 3 * X (-2) * X (-1)) * e2_m2
    + (2) * (b ^ 6 * c ^ 6 * d ^ 3 * X (-2) * X (-1)) * e2_m2
    - (b ^ 18 * d ^ 4 * X (-2) * X (-1)) * e2_m2
    + (-3) * (b ^ 10 * c ^ 3 * d ^ 4 * X (-2) * X (-1)) * e2_m2
    - (b ^ 2 * c ^ 6 * d ^ 4 * X (-2) * X (-1)) * e2_m2
    + (b ^ 14 * d ^ 5 * X (-2) * X (-1)) * e2_m2
    + (2) * (b ^ 6 * c ^ 3 * d ^ 5 * X (-2) * X (-1)) * e2_m2
    - (b ^ 10 * d ^ 6 * X (-2) * X (-1)) * e2_m2
    - (c ^ 3 * d ^ 3 * X (-7) * X 2) * e2_m1
    + (-3) * (b ^ 4 * c ^ 8 * X (-6) * X 1) * e2_m1
    + (3) * (b ^ 8 * c ^ 5 * d * X (-6) * X 1) * e2_m1
    - (b ^ 12 * c ^ 2 * d ^ 2 * X (-6) * X 1) * e2_m1
    + (-2) * (b ^ 4 * c ^ 5 * d ^ 2 * X (-6) * X 1) * e2_m1
    + (b ^ 8 * c ^ 2 * d ^ 3 * X (-6) * X 1) * e2_m1
    + (-3) * (b ^ 4 * c ^ 8 * d * X (-5) * X 0) * e2_m1
    + (3) * (b ^ 8 * c ^ 5 * d ^ 2 * X (-5) * X 0) * e2_m1
    - (b ^ 12 * c ^ 2 * d ^ 3 * X (-5) * X 0) * e2_m1
    - (b ^ 4 * c ^ 5 * d ^ 3 * X (-5) * X 0) * e2_m1
    + (3) * (b ^ 4 * c ^ 9 * d * X (-4) * X (-1)) * e2_m1
    + (-3) * (b ^ 8 * c ^ 6 * d ^ 2 * X (-4) * X (-1)) * e2_m1
    + (b ^ 12 * c ^ 3 * d ^ 3 * X (-4) * X (-1)) * e2_m1
    + (2) * (b ^ 4 * c ^ 6 * d ^ 3 * X (-4) * X (-1)) * e2_m1
    + (-2) * (b ^ 8 * c ^ 3 * d ^ 4 * X (-4) * X (-1)) * e2_m1
    + (b ^ 12 * d ^ 5 * X (-4) * X (-1)) * e2_m1
    + (b ^ 4 * c ^ 3 * d ^ 5 * X (-4) * X (-1)) * e2_m1
    - (b ^ 8 * d ^ 6 * X (-4) * X (-1)) * e2_m1
    + (-3) * (b ^ 4 * c ^ 11 * X (-3) * X (-2)) * e2_m1
    + (9) * (b ^ 8 * c ^ 8 * d * X (-3) * X (-2)) * e2_m1
    + (-10) * (b ^ 12 * c ^ 5 * d ^ 2 * X (-3) * X (-2)) * e2_m1
    + (-2) * (b ^ 4 * c ^ 8 * d ^ 2 * X (-3) * X (-2)) * e2_m1
    + (5) * (b ^ 16 * c ^ 2 * d ^ 3 * X (-3) * X (-2)) * e2_m1
    + (5) * (b ^ 8 * c ^ 5 * d ^ 3 * X (-3) * X (-2)) * e2_m1
    + (c ^ 8 * d ^ 3 * X (-3) * X (-2)) * e2_m1
    + (-4) * (b ^ 12 * c ^ 2 * d ^ 4 * X (-3) * X (-2)) * e2_m1
    + (-3) * (b ^ 4 * c ^ 5 * d ^ 4 * X (-3) * X (-2)) * e2_m1
    + (3) * (b ^ 8 * c ^ 2 * d ^ 5 * X (-3) * X (-2)) * e2_m1
    + (-3) * (b ^ 2 * c ^ 9 * X (-6) * X (-1)) * e2_0
    + (3) * (b ^ 6 * c ^ 6 * d * X (-6) * X (-1)) * e2_0
    - (b ^ 10 * c ^ 3 * d ^ 2 * X (-6) * X (-1)) * e2_0
    + (-2) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-6) * X (-1)) * e2_0
    + (b ^ 6 * c ^ 3 * d ^ 3 * X (-6) * X (-1)) * e2_0
    + (3) * (b ^ 2 * c ^ 10 * X (-5) * X (-2)) * e2_0
    + (-2) * (b ^ 10 * c ^ 4 * d ^ 2 * X (-5) * X (-2)) * e2_0
    + (2) * (b ^ 2 * c ^ 7 * d ^ 2 * X (-5) * X (-2)) * e2_0
    + (b ^ 14 * c * d ^ 3 * X (-5) * X (-2)) * e2_0
    + (b ^ 6 * c ^ 4 * d ^ 3 * X (-5) * X (-2)) * e2_0
    - (b ^ 10 * c * d ^ 4 * X (-5) * X (-2)) * e2_0
    + (3) * (b ^ 6 * c ^ 9 * X (-4) * X (-3)) * e2_0
    + (-6) * (b ^ 10 * c ^ 6 * d * X (-4) * X (-3)) * e2_0
    + (b ^ 2 * c ^ 9 * d * X (-4) * X (-3)) * e2_0
    + (4) * (b ^ 14 * c ^ 3 * d ^ 2 * X (-4) * X (-3)) * e2_0
    + (-2) * (b ^ 10 * c ^ 3 * d ^ 3 * X (-4) * X (-3)) * e2_0
    + (b ^ 2 * c ^ 6 * d ^ 3 * X (-4) * X (-3)) * e2_0
    - (b ^ 6 * c ^ 3 * d ^ 4 * X (-4) * X (-3)) * e2_0
    + (b ^ 10 * d ^ 5 * X (-4) * X (-3)) * e2_0
    + (b ^ 2 * c ^ 3 * d ^ 5 * X (-4) * X (-3)) * e2_0
    + (b ^ 4 * c ^ 3 * d ^ 2 * X (-7) * X (-2)) * e2_1
    + (3) * (b ^ 4 * c ^ 7 * X (-6) * X (-3)) * e2_1
    + (-3) * (b ^ 8 * c ^ 4 * d * X (-6) * X (-3)) * e2_1
    + (b ^ 12 * c * d ^ 2 * X (-6) * X (-3)) * e2_1
    + (b ^ 4 * c ^ 4 * d ^ 2 * X (-6) * X (-3)) * e2_1
    - (b ^ 8 * c * d ^ 3 * X (-6) * X (-3)) * e2_1
    + (c ^ 6 * d ^ 2 * X (-5) * X (-4)) * e2_1
    - (b ^ 4 * c ^ 3 * d ^ 3 * X (-5) * X (-4)) * e2_1
    + (b ^ 8 * d ^ 4 * X (-5) * X (-4)) * e2_1
    + (c ^ 6 * X (-3) * X 4) * e3_m4
    - (b ^ 4 * c ^ 3 * d ^ 2 * X (-2) * X 3) * e3_m4
    - (b ^ 4 * c ^ 4 * d ^ 2 * X (-1) * X 2) * e3_m4
    + (b ^ 8 * c * d ^ 3 * X (-1) * X 2) * e3_m4
    + (c ^ 4 * d ^ 3 * X (-1) * X 2) * e3_m4
    - (b ^ 4 * c * d ^ 4 * X (-1) * X 2) * e3_m4
    + (-3) * (b ^ 2 * c ^ 7 * X (-4) * X 3) * e3_m3
    + (3) * (b ^ 6 * c ^ 4 * d * X (-4) * X 3) * e3_m3
    - (b ^ 10 * c * d ^ 2 * X (-4) * X 3) * e3_m3
    - (b ^ 2 * c ^ 4 * d ^ 2 * X (-4) * X 3) * e3_m3
    + (b ^ 6 * c * d ^ 3 * X (-4) * X 3) * e3_m3
    + (3) * (b ^ 6 * c ^ 7 * X (-3) * X 2) * e3_m3
    + (-3) * (b ^ 10 * c ^ 4 * d * X (-3) * X 2) * e3_m3
    + (b ^ 2 * c ^ 7 * d * X (-3) * X 2) * e3_m3
    + (b ^ 14 * c * d ^ 2 * X (-3) * X 2) * e3_m3
    + (b ^ 6 * c ^ 4 * d ^ 2 * X (-3) * X 2) * e3_m3
    - (b ^ 10 * c * d ^ 3 * X (-3) * X 2) * e3_m3
    + (-6) * (b ^ 6 * c ^ 8 * X (-2) * X 1) * e3_m3
    + (9) * (b ^ 10 * c ^ 5 * d * X (-2) * X 1) * e3_m3
    + (-5) * (b ^ 14 * c ^ 2 * d ^ 2 * X (-2) * X 1) * e3_m3
    + (-4) * (b ^ 6 * c ^ 5 * d ^ 2 * X (-2) * X 1) * e3_m3
    + (4) * (b ^ 10 * c ^ 2 * d ^ 3 * X (-2) * X 1) * e3_m3
    + (b ^ 2 * c ^ 5 * d ^ 3 * X (-2) * X 1) * e3_m3
    + (-2) * (b ^ 6 * c ^ 2 * d ^ 4 * X (-2) * X 1) * e3_m3
    + (3) * (b ^ 2 * c ^ 10 * X (-1) * X 0) * e3_m3
    + (-3) * (b ^ 6 * c ^ 7 * d * X (-1) * X 0) * e3_m3
    + (b ^ 10 * c ^ 4 * d ^ 2 * X (-1) * X 0) * e3_m3
    + (2) * (b ^ 2 * c ^ 7 * d ^ 2 * X (-1) * X 0) * e3_m3
    - (b ^ 6 * c ^ 4 * d ^ 3 * X (-1) * X 0) * e3_m3
    + (c ^ 4 * X (-7) * X 4) * e3_m2
    - (c ^ 7 * d ^ 2 * X (-4) * X 1) * e3_m2
    + (2) * (b ^ 4 * c ^ 4 * d ^ 3 * X (-4) * X 1) * e3_m2
    - (b ^ 8 * c * d ^ 4 * X (-4) * X 1) * e3_m2
    + (3) * (b ^ 8 * c ^ 8 * X (-3) * X 0) * e3_m2
    + (-6) * (b ^ 12 * c ^ 5 * d * X (-3) * X 0) * e3_m2
    + (3) * (b ^ 4 * c ^ 8 * d * X (-3) * X 0) * e3_m2
    + (4) * (b ^ 16 * c ^ 2 * d ^ 2 * X (-3) * X 0) * e3_m2
    - (b ^ 8 * c ^ 5 * d ^ 2 * X (-3) * X 0) * e3_m2
    + (-2) * (b ^ 12 * c ^ 2 * d ^ 3 * X (-3) * X 0) * e3_m2
    + (2) * (b ^ 8 * c ^ 2 * d ^ 4 * X (-3) * X 0) * e3_m2
    + (-3) * (b ^ 4 * c ^ 10 * X (-2) * X (-1)) * e3_m2
    + (6) * (b ^ 8 * c ^ 7 * d * X (-2) * X (-1)) * e3_m2
    + (-4) * (b ^ 12 * c ^ 4 * d ^ 2 * X (-2) * X (-1)) * e3_m2
    + (-2) * (b ^ 4 * c ^ 7 * d ^ 2 * X (-2) * X (-1)) * e3_m2
    + (b ^ 16 * c * d ^ 3 * X (-2) * X (-1)) * e3_m2
    + (3) * (b ^ 8 * c ^ 4 * d ^ 3 * X (-2) * X (-1)) * e3_m2
    + (c ^ 7 * d ^ 3 * X (-2) * X (-1)) * e3_m2
    - (b ^ 12 * c * d ^ 4 * X (-2) * X (-1)) * e3_m2
    + (-2) * (b ^ 4 * c ^ 4 * d ^ 4 * X (-2) * X (-1)) * e3_m2
    + (b ^ 8 * c * d ^ 5 * X (-2) * X (-1)) * e3_m2
    + (b ^ 2 * c ^ 4 * d * X (-7) * X 2) * e3_m1
    - (b ^ 6 * c * d ^ 2 * X (-7) * X 2) * e3_m1
    + (b ^ 2 * c * d ^ 3 * X (-7) * X 2) * e3_m1
    + (3) * (b ^ 2 * c ^ 9 * X (-5) * X 0) * e3_m1
    + (-2) * (b ^ 10 * c ^ 3 * d ^ 2 * X (-5) * X 0) * e3_m1
    + (2) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-5) * X 0) * e3_m1
    + (b ^ 14 * d ^ 3 * X (-5) * X 0) * e3_m1
    + (-3) * (b ^ 2 * c ^ 10 * X (-4) * X (-1)) * e3_m1
    + (3) * (b ^ 6 * c ^ 7 * d * X (-4) * X (-1)) * e3_m1
    - (b ^ 10 * c ^ 4 * d ^ 2 * X (-4) * X (-1)) * e3_m1
    + (-2) * (b ^ 2 * c ^ 7 * d ^ 2 * X (-4) * X (-1)) * e3_m1
    + (2) * (b ^ 6 * c ^ 4 * d ^ 3 * X (-4) * X (-1)) * e3_m1
    - (b ^ 10 * c * d ^ 4 * X (-4) * X (-1)) * e3_m1
    - (b ^ 2 * c ^ 4 * d ^ 4 * X (-4) * X (-1)) * e3_m1
    + (b ^ 6 * c * d ^ 5 * X (-4) * X (-1)) * e3_m1
    - (b ^ 18 * d ^ 3 * X (-3) * X (-2)) * e3_m1
    + (b ^ 14 * d ^ 4 * X (-3) * X (-2)) * e3_m1
    - (b ^ 10 * d ^ 5 * X (-3) * X (-2)) * e3_m1
    + (-3) * (b ^ 4 * c ^ 8 * X (-5) * X (-2)) * e3_0
    + (3) * (b ^ 8 * c ^ 5 * d * X (-5) * X (-2)) * e3_0
    - (b ^ 12 * c ^ 2 * d ^ 2 * X (-5) * X (-2)) * e3_0
    + (-2) * (b ^ 4 * c ^ 5 * d ^ 2 * X (-5) * X (-2)) * e3_0
    + (b ^ 8 * c ^ 2 * d ^ 3 * X (-5) * X (-2)) * e3_0
    + (c ^ 10 * X (-4) * X (-3)) * e3_0
    + (c ^ 7 * d ^ 2 * X (-4) * X (-3)) * e3_0
    - (b ^ 2 * c ^ 4 * d * X (-7) * X (-2)) * e3_1
    + (b ^ 2 * c ^ 5 * d * X (-6) * X (-3)) * e3_1
    - (b ^ 2 * c ^ 4 * d ^ 2 * X (-5) * X (-4)) * e3_1
    - (c ^ 4 * X (-5) * X 4) * e4_m3
    + (c ^ 6 * X (-4) * X 3) * e4_m3
    + (-2) * (b ^ 4 * c ^ 3 * d * X (-4) * X 3) * e4_m3
    + (b ^ 8 * d ^ 2 * X (-4) * X 3) * e4_m3
    + (c ^ 3 * d ^ 3 * X (-3) * X 2) * e4_m3
    + (X (-7) * X (-4)) * e5_2

lemma cert_b {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - (d * b) ^ 2 * X (j + 1) * X (j - 1) + (d * b ^ 4 - c ^ 3) * c * X j ^ 2 = 0)
    (_h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - (d * b ^ 4 - c ^ 3) ^ 2 * X (j + 1) * X (j - 1) + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X j ^ 2 = 0)
    (_h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * X j ^ 2 = 0) :
    X 1 * X 2 * (X 7 * X (-7)
      - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * X 1 * X (-1)
      + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X 0 ^ 2) = 0 := by
  have e2_m3 := h2 (-3)
  have e2_m2 := h2 (-2)
  have e2_m1 := h2 (-1)
  have e2_0 := h2 0
  have e2_1 := h2 1
  have e2_2 := h2 2
  have e2_3 := h2 3
  have e2_4 := h2 4
  have e3_m3 := h3 (-3)
  have e3_m2 := h3 (-2)
  have e3_m1 := h3 (-1)
  have e3_0 := h3 0
  have e3_1 := h3 1
  have e3_2 := h3 2
  have e3_3 := h3 3
  have e3_4 := h3 4
  have e4_m3 := h4 (-3)
  have e4_m2 := h4 (-2)
  have e4_m1 := h4 (-1)
  have e4_0 := h4 0
  have e4_3 := h4 3
  norm_num at e2_m3 e2_m2 e2_m1 e2_0 e2_1 e2_2 e2_3 e2_4 e3_m3 e3_m2 e3_m1 e3_0 e3_1 e3_2 e3_3 e3_4 e4_m3 e4_m2 e4_m1 e4_0 e4_3
  linear_combination
    (c ^ 3 * X 2 * X 7) * e2_m3
    + (b ^ 4 * d * X 2 * X 7) * e2_m3
    + (-3) * (c ^ 4 * X 3 * X 6) * e2_m3
    + (3) * (b ^ 4 * d ^ 2 * X 4 * X 5) * e2_m3
    + (b ^ 2 * c ^ 4 * X 0 * X 7) * e2_m2
    - (b ^ 6 * c * d * X 0 * X 7) * e2_m2
    - (b ^ 2 * c * d ^ 2 * X 0 * X 7) * e2_m2
    + (2) * (b ^ 2 * c ^ 4 * d * X 1 * X 6) * e2_m2
    + (2) * (b ^ 2 * c * d ^ 3 * X 1 * X 6) * e2_m2
    + (-3) * (b ^ 2 * c ^ 5 * d * X 2 * X 5) * e2_m2
    - (b ^ 2 * c ^ 7 * X 3 * X 4) * e2_m2
    + (2) * (b ^ 6 * c ^ 4 * d * X 3 * X 4) * e2_m2
    + (3) * (b ^ 6 * c * d ^ 3 * X 3 * X 4) * e2_m2
    + (2) * (b ^ 2 * c * d ^ 4 * X 3 * X 4) * e2_m2
    + (2) * (c ^ 7 * X (-1) * X 6) * e2_m1
    + (-3) * (b ^ 4 * c ^ 4 * d * X (-1) * X 6) * e2_m1
    + (2) * (b ^ 8 * c * d ^ 2 * X (-1) * X 6) * e2_m1
    + (-2) * (c ^ 4 * d ^ 2 * X (-1) * X 6) * e2_m1
    + (2) * (b ^ 4 * c * d ^ 3 * X (-1) * X 6) * e2_m1
    - (c ^ 7 * d * X 0 * X 5) * e2_m1
    + (b ^ 4 * c ^ 4 * d ^ 2 * X 0 * X 5) * e2_m1
    + (-2) * (b ^ 8 * c * d ^ 3 * X 0 * X 5) * e2_m1
    - (b ^ 4 * c * d ^ 4 * X 0 * X 5) * e2_m1
    - (c ^ 8 * d * X 1 * X 4) * e2_m1
    + (2) * (b ^ 4 * c ^ 5 * d ^ 2 * X 1 * X 4) * e2_m1
    - (b ^ 8 * c ^ 2 * d ^ 3 * X 1 * X 4) * e2_m1
    + (c ^ 5 * d ^ 3 * X 1 * X 4) * e2_m1
    + (b ^ 4 * c ^ 2 * d ^ 4 * X 1 * X 4) * e2_m1
    + (2) * (c ^ 10 * X 2 * X 3) * e2_m1
    + (-4) * (b ^ 4 * c ^ 7 * d * X 2 * X 3) * e2_m1
    + (2) * (b ^ 8 * c ^ 4 * d ^ 2 * X 2 * X 3) * e2_m1
    - (c ^ 7 * d ^ 2 * X 2 * X 3) * e2_m1
    + (b ^ 12 * c * d ^ 3 * X 2 * X 3) * e2_m1
    + (2) * (b ^ 8 * c * d ^ 4 * X 2 * X 3) * e2_m1
    - (c ^ 4 * d ^ 4 * X 2 * X 3) * e2_m1
    - (b ^ 2 * c ^ 3 * X (-4) * X 7) * e2_0
    + (b ^ 6 * d * X (-4) * X 7) * e2_0
    + (b ^ 2 * d ^ 2 * X (-4) * X 7) * e2_0
    - (b ^ 2 * c ^ 4 * d * X (-3) * X 6) * e2_0
    + (2) * (b ^ 6 * c * d ^ 2 * X (-3) * X 6) * e2_0
    - (b ^ 2 * c * d ^ 3 * X (-3) * X 6) * e2_0
    - (b ^ 2 * c ^ 6 * d * X (-2) * X 5) * e2_0
    + (2) * (b ^ 6 * c ^ 3 * d ^ 2 * X (-2) * X 5) * e2_0
    + (-2) * (b ^ 6 * d ^ 4 * X (-2) * X 5) * e2_0
    + (b ^ 2 * c ^ 9 * X (-1) * X 4) * e2_0
    + (-2) * (b ^ 6 * c ^ 6 * d * X (-1) * X 4) * e2_0
    + (3) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-1) * X 4) * e2_0
    + (-3) * (b ^ 6 * c ^ 3 * d ^ 3 * X (-1) * X 4) * e2_0
    + (-2) * (b ^ 10 * d ^ 4 * X (-1) * X 4) * e2_0
    + (-5) * (b ^ 2 * c ^ 3 * d ^ 4 * X (-1) * X 4) * e2_0
    + (b ^ 6 * d ^ 5 * X (-1) * X 4) * e2_0
    - (b ^ 6 * c ^ 7 * d * X 0 * X 3) * e2_0
    + (2) * (b ^ 10 * c ^ 4 * d ^ 2 * X 0 * X 3) * e2_0
    - (b ^ 14 * c * d ^ 3 * X 0 * X 3) * e2_0
    + (-2) * (b ^ 6 * c ^ 4 * d ^ 3 * X 0 * X 3) * e2_0
    + (3) * (b ^ 10 * c * d ^ 4 * X 0 * X 3) * e2_0
    + (2) * (b ^ 6 * c * d ^ 5 * X 0 * X 3) * e2_0
    + (3) * (b ^ 2 * c ^ 9 * d * X 1 * X 2) * e2_0
    + (-6) * (b ^ 6 * c ^ 6 * d ^ 2 * X 1 * X 2) * e2_0
    + (4) * (b ^ 10 * c ^ 3 * d ^ 3 * X 1 * X 2) * e2_0
    + (b ^ 6 * c ^ 3 * d ^ 4 * X 1 * X 2) * e2_0
    - (c * X (-6) * X 7) * e2_1
    + (c ^ 4 * X (-5) * X 6) * e2_1
    + (b ^ 4 * c * d * X (-5) * X 6) * e2_1
    + (2) * (c * d ^ 2 * X (-5) * X 6) * e2_1
    - (b ^ 4 * c ^ 2 * d ^ 2 * X (-4) * X 5) * e2_1
    + (c ^ 2 * d ^ 3 * X (-4) * X 5) * e2_1
    + (c ^ 7 * d * X (-3) * X 4) * e2_1
    - (b ^ 4 * c ^ 4 * d ^ 2 * X (-3) * X 4) * e2_1
    - (b ^ 8 * c * d ^ 3 * X (-3) * X 4) * e2_1
    - (c ^ 4 * d ^ 3 * X (-3) * X 4) * e2_1
    + (-2) * (b ^ 4 * c ^ 7 * d * X (-2) * X 3) * e2_1
    + (4) * (b ^ 8 * c ^ 4 * d ^ 2 * X (-2) * X 3) * e2_1
    + (-2) * (b ^ 12 * c * d ^ 3 * X (-2) * X 3) * e2_1
    - (b ^ 4 * c ^ 4 * d ^ 3 * X (-2) * X 3) * e2_1
    + (b ^ 8 * c * d ^ 4 * X (-2) * X 3) * e2_1
    + (2) * (b ^ 4 * c * d ^ 5 * X (-2) * X 3) * e2_1
    + (-2) * (c ^ 11 * X (-1) * X 2) * e2_1
    + (5) * (b ^ 4 * c ^ 8 * d * X (-1) * X 2) * e2_1
    + (-5) * (b ^ 8 * c ^ 5 * d ^ 2 * X (-1) * X 2) * e2_1
    + (c ^ 8 * d ^ 2 * X (-1) * X 2) * e2_1
    + (b ^ 12 * c ^ 2 * d ^ 3 * X (-1) * X 2) * e2_1
    + (-3) * (b ^ 8 * c ^ 2 * d ^ 4 * X (-1) * X 2) * e2_1
    + (c ^ 5 * d ^ 4 * X (-1) * X 2) * e2_1
    + (-3) * (b ^ 4 * c ^ 2 * d ^ 5 * X (-1) * X 2) * e2_1
    + (2) * (b ^ 4 * c ^ 4 * d ^ 4 * X 0 * X 1) * e2_1
    + (-2) * (b ^ 8 * c * d ^ 5 * X 0 * X 1) * e2_1
    + (3) * (b ^ 2 * c * d * X (-6) * X 5) * e2_2
    + (b ^ 2 * c ^ 2 * d ^ 2 * X (-5) * X 4) * e2_2
    + (b ^ 2 * c ^ 7 * X (-4) * X 3) * e2_2
    + (-2) * (b ^ 6 * c ^ 4 * d * X (-4) * X 3) * e2_2
    + (-3) * (b ^ 6 * c * d ^ 3 * X (-4) * X 3) * e2_2
    + (-2) * (b ^ 2 * c * d ^ 4 * X (-4) * X 3) * e2_2
    - (b ^ 2 * c ^ 7 * d * X (-3) * X 2) * e2_2
    + (2) * (b ^ 6 * c ^ 4 * d ^ 2 * X (-3) * X 2) * e2_2
    + (b ^ 6 * c * d ^ 4 * X (-3) * X 2) * e2_2
    + (-3) * (b ^ 2 * c ^ 8 * d * X (-2) * X 1) * e2_2
    + (6) * (b ^ 6 * c ^ 5 * d ^ 2 * X (-2) * X 1) * e2_2
    + (-4) * (b ^ 10 * c ^ 2 * d ^ 3 * X (-2) * X 1) * e2_2
    - (b ^ 6 * c ^ 2 * d ^ 4 * X (-2) * X 1) * e2_2
    - (b ^ 2 * c ^ 10 * X (-1) * X 0) * e2_2
    + (3) * (b ^ 6 * c ^ 7 * d * X (-1) * X 0) * e2_2
    + (-3) * (b ^ 10 * c ^ 4 * d ^ 2 * X (-1) * X 0) * e2_2
    + (-2) * (b ^ 2 * c ^ 7 * d ^ 2 * X (-1) * X 0) * e2_2
    + (b ^ 14 * c * d ^ 3 * X (-1) * X 0) * e2_2
    + (5) * (b ^ 6 * c ^ 4 * d ^ 3 * X (-1) * X 0) * e2_2
    + (-3) * (b ^ 10 * c * d ^ 4 * X (-1) * X 0) * e2_2
    + (4) * (b ^ 2 * c ^ 4 * d ^ 4 * X (-1) * X 0) * e2_2
    + (-4) * (b ^ 6 * c * d ^ 5 * X (-1) * X 0) * e2_2
    + (c ^ 4 * X (-6) * X 3) * e2_3
    + (2) * (b ^ 4 * c * d * X (-6) * X 3) * e2_3
    - (c ^ 6 * X (-5) * X 2) * e2_3
    - (b ^ 4 * c ^ 3 * d * X (-5) * X 2) * e2_3
    + (-2) * (b ^ 4 * d ^ 3 * X (-5) * X 2) * e2_3
    + (4) * (b ^ 4 * c ^ 3 * d ^ 2 * X (-4) * X 1) * e2_3
    + (-3) * (b ^ 8 * d ^ 3 * X (-4) * X 1) * e2_3
    - (c ^ 3 * d ^ 3 * X (-4) * X 1) * e2_3
    + (c ^ 7 * d * X (-3) * X 0) * e2_3
    - (b ^ 4 * c ^ 4 * d ^ 2 * X (-3) * X 0) * e2_3
    + (2) * (b ^ 8 * c * d ^ 3 * X (-3) * X 0) * e2_3
    + (b ^ 4 * c * d ^ 4 * X (-3) * X 0) * e2_3
    + (b ^ 4 * c ^ 3 * d ^ 3 * X (-2) * X (-1)) * e2_3
    + (-2) * (b ^ 8 * d ^ 4 * X (-2) * X (-1)) * e2_3
    - (b ^ 2 * c * d * X (-6) * X 1) * e2_4
    + (b ^ 6 * c ^ 2 * d * X (-4) * X (-1)) * e2_4
    + (b ^ 2 * c ^ 4 * d * X (-3) * X (-2)) * e2_4
    + (-2) * (b ^ 6 * c * d ^ 2 * X (-3) * X (-2)) * e2_4
    + (b ^ 2 * c * d ^ 3 * X (-3) * X (-2)) * e2_4
    + (-2) * (b ^ 2 * c * X 2 * X 7) * e3_m3
    + (3) * (b ^ 2 * c ^ 2 * X 3 * X 6) * e3_m3
    + (-3) * (b ^ 2 * c * d * X 4 * X 5) * e3_m3
    + (c ^ 2 * d * X 0 * X 7) * e3_m2
    - (c ^ 5 * X 1 * X 6) * e3_m2
    - (b ^ 4 * c ^ 2 * d * X 1 * X 6) * e3_m2
    + (-2) * (c ^ 2 * d ^ 2 * X 1 * X 6) * e3_m2
    + (c ^ 6 * X 2 * X 5) * e3_m2
    + (b ^ 4 * c ^ 3 * d * X 2 * X 5) * e3_m2
    + (2) * (b ^ 4 * d ^ 3 * X 2 * X 5) * e3_m2
    + (-2) * (b ^ 4 * c ^ 2 * d ^ 2 * X 3 * X 4) * e3_m2
    - (b ^ 6 * c ^ 2 * d * X (-1) * X 6) * e3_m1
    + (2) * (b ^ 6 * c ^ 2 * d ^ 2 * X 0 * X 5) * e3_m1
    + (b ^ 2 * c ^ 2 * d ^ 3 * X 0 * X 5) * e3_m1
    + (-2) * (b ^ 2 * c ^ 6 * d * X 1 * X 4) * e3_m1
    + (4) * (b ^ 6 * c ^ 3 * d ^ 2 * X 1 * X 4) * e3_m1
    + (-3) * (b ^ 10 * d ^ 3 * X 1 * X 4) * e3_m1
    + (-3) * (b ^ 2 * c ^ 3 * d ^ 3 * X 1 * X 4) * e3_m1
    - (b ^ 2 * c ^ 8 * X 2 * X 3) * e3_m1
    + (3) * (b ^ 6 * c ^ 5 * d * X 2 * X 3) * e3_m1
    + (-2) * (b ^ 10 * c ^ 2 * d ^ 2 * X 2 * X 3) * e3_m1
    + (b ^ 6 * c ^ 2 * d ^ 3 * X 2 * X 3) * e3_m1
    + (3) * (b ^ 2 * c ^ 2 * d ^ 4 * X 2 * X 3) * e3_m1
    + (3) * (c ^ 5 * X (-3) * X 6) * e3_0
    + (-3) * (b ^ 4 * c ^ 2 * d * X (-3) * X 6) * e3_0
    + (b ^ 4 * c ^ 4 * d * X (-2) * X 5) * e3_0
    + (-2) * (b ^ 8 * c * d ^ 2 * X (-2) * X 5) * e3_0
    + (b ^ 4 * c * d ^ 3 * X (-2) * X 5) * e3_0
    - (b ^ 4 * c ^ 7 * X (-1) * X 4) * e3_0
    + (2) * (b ^ 8 * c ^ 4 * d * X (-1) * X 4) * e3_0
    - (c ^ 7 * d * X (-1) * X 4) * e3_0
    + (-3) * (b ^ 4 * c ^ 4 * d ^ 2 * X (-1) * X 4) * e3_0
    + (6) * (b ^ 8 * c * d ^ 3 * X (-1) * X 4) * e3_0
    + (c ^ 4 * d ^ 3 * X (-1) * X 4) * e3_0
    + (3) * (b ^ 4 * c * d ^ 4 * X (-1) * X 4) * e3_0
    + (b ^ 4 * c ^ 8 * X 0 * X 3) * e3_0
    + (-2) * (b ^ 8 * c ^ 5 * d * X 0 * X 3) * e3_0
    + (b ^ 12 * c ^ 2 * d ^ 2 * X 0 * X 3) * e3_0
    + (2) * (b ^ 4 * c ^ 5 * d ^ 2 * X 0 * X 3) * e3_0
    + (-3) * (b ^ 8 * c ^ 2 * d ^ 3 * X 0 * X 3) * e3_0
    + (-2) * (b ^ 4 * c ^ 2 * d ^ 4 * X 0 * X 3) * e3_0
    - (c ^ 10 * X 1 * X 2) * e3_0
    + (b ^ 4 * c ^ 7 * d * X 1 * X 2) * e3_0
    + (c ^ 7 * d ^ 2 * X 1 * X 2) * e3_0
    - (b ^ 12 * c * d ^ 3 * X 1 * X 2) * e3_0
    - (b ^ 4 * c ^ 4 * d ^ 3 * X 1 * X 2) * e3_0
    - (b ^ 8 * c * d ^ 4 * X 1 * X 2) * e3_0
    + (c ^ 4 * d ^ 4 * X 1 * X 2) * e3_0
    + (-3) * (b ^ 2 * c ^ 3 * d * X (-4) * X 5) * e3_1
    + (3) * (b ^ 6 * d ^ 2 * X (-4) * X 5) * e3_1
    - (b ^ 2 * c ^ 5 * d * X (-3) * X 4) * e3_1
    + (2) * (b ^ 6 * c ^ 2 * d ^ 2 * X (-3) * X 4) * e3_1
    - (b ^ 2 * c ^ 2 * d ^ 3 * X (-3) * X 4) * e3_1
    - (b ^ 2 * c ^ 8 * X (-2) * X 3) * e3_1
    + (2) * (b ^ 6 * c ^ 5 * d * X (-2) * X 3) * e3_1
    + (-2) * (b ^ 10 * c ^ 2 * d ^ 2 * X (-2) * X 3) * e3_1
    + (b ^ 2 * c ^ 5 * d ^ 2 * X (-2) * X 3) * e3_1
    + (-2) * (b ^ 6 * c ^ 2 * d ^ 3 * X (-2) * X 3) * e3_1
    + (-2) * (b ^ 2 * c ^ 2 * d ^ 4 * X (-2) * X 3) * e3_1
    + (b ^ 2 * c ^ 9 * X (-1) * X 2) * e3_1
    + (-2) * (b ^ 6 * c ^ 6 * d * X (-1) * X 2) * e3_1
    + (2) * (b ^ 10 * c ^ 3 * d ^ 2 * X (-1) * X 2) * e3_1
    + (-3) * (b ^ 2 * c ^ 6 * d ^ 2 * X (-1) * X 2) * e3_1
    + (5) * (b ^ 6 * c ^ 3 * d ^ 3 * X (-1) * X 2) * e3_1
    + (3) * (b ^ 2 * c ^ 3 * d ^ 4 * X (-1) * X 2) * e3_1
    - (b ^ 6 * d ^ 5 * X (-1) * X 2) * e3_1
    + (-2) * (b ^ 2 * c ^ 5 * d ^ 3 * X 0 * X 1) * e3_1
    + (2) * (b ^ 6 * c ^ 2 * d ^ 4 * X 0 * X 1) * e3_1
    + (-3) * (b ^ 4 * d ^ 2 * X (-5) * X 4) * e3_2
    - (b ^ 4 * c ^ 5 * X (-4) * X 3) * e3_2
    + (2) * (b ^ 8 * c ^ 2 * d * X (-4) * X 3) * e3_2
    + (2) * (b ^ 4 * c ^ 2 * d ^ 2 * X (-4) * X 3) * e3_2
    - (c ^ 2 * d ^ 3 * X (-4) * X 3) * e3_2
    + (c ^ 8 * X (-3) * X 2) * e3_2
    + (-2) * (b ^ 4 * c ^ 5 * d * X (-3) * X 2) * e3_2
    - (b ^ 4 * c ^ 2 * d ^ 3 * X (-3) * X 2) * e3_2
    + (-3) * (b ^ 2 * c ^ 2 * X (-6) * X 3) * e3_3
    + (b ^ 2 * c ^ 4 * X (-5) * X 2) * e3_3
    + (b ^ 6 * c * d * X (-5) * X 2) * e3_3
    + (2) * (b ^ 2 * c * d ^ 2 * X (-5) * X 2) * e3_3
    + (-2) * (b ^ 2 * c ^ 4 * d * X (-4) * X 1) * e3_3
    + (-2) * (b ^ 2 * c * d ^ 3 * X (-4) * X 1) * e3_3
    + (-2) * (b ^ 2 * c ^ 5 * d * X (-3) * X 0) * e3_3
    + (b ^ 6 * c ^ 2 * d ^ 2 * X (-3) * X 0) * e3_3
    + (b ^ 2 * c ^ 2 * d ^ 3 * X (-3) * X 0) * e3_3
    + (2) * (b ^ 2 * c ^ 7 * X (-2) * X (-1)) * e3_3
    + (-4) * (b ^ 6 * c ^ 4 * d * X (-2) * X (-1)) * e3_3
    + (2) * (b ^ 10 * c * d ^ 2 * X (-2) * X (-1)) * e3_3
    + (b ^ 6 * c * d ^ 3 * X (-2) * X (-1)) * e3_3
    + (-2) * (b ^ 2 * c * d ^ 4 * X (-2) * X (-1)) * e3_3
    + (c ^ 2 * X (-6) * X 1) * e3_4
    - (c ^ 2 * d * X (-5) * X 0) * e3_4
    - (b ^ 4 * c ^ 3 * X (-4) * X (-1)) * e3_4
    + (b ^ 8 * d * X (-4) * X (-1)) * e3_4
    + (b ^ 4 * d ^ 2 * X (-4) * X (-1)) * e3_4
    + (X 2 * X 7) * e4_m3
    + (b ^ 2 * c * X 0 * X 7) * e4_m2
    + (b ^ 2 * c * d * X 1 * X 6) * e4_m2
    + (-3) * (b ^ 2 * c ^ 2 * d * X 2 * X 5) * e4_m2
    + (-2) * (b ^ 2 * c ^ 4 * X 3 * X 4) * e4_m2
    + (2) * (b ^ 6 * c * d * X 3 * X 4) * e4_m2
    + (b ^ 2 * c * d ^ 2 * X 3 * X 4) * e4_m2
    + (2) * (c ^ 4 * X (-1) * X 6) * e4_m1
    - (b ^ 4 * c * d * X (-1) * X 6) * e4_m1
    + (-2) * (c * d ^ 2 * X (-1) * X 6) * e4_m1
    - (c ^ 4 * d * X 0 * X 5) * e4_m1
    - (b ^ 10 * d ^ 2 * X (-1) * X 4) * e4_0
    - (b ^ 6 * d ^ 3 * X (-1) * X 4) * e4_0
    + (c * X (-6) * X 3) * e4_3
    - (c ^ 3 * X (-5) * X 2) * e4_3
    - (b ^ 4 * d * X (-5) * X 2) * e4_3
    + (b ^ 4 * c ^ 4 * X (-3) * X 0) * e4_3
    - (b ^ 8 * c * d * X (-3) * X 0) * e4_3
    + (c ^ 4 * d * X (-3) * X 0) * e4_3


section Gen

variable {R : Type} [CommRing R] [IsDomain R] (b c d : R)

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
lemma n5 : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
  have h := normEDS_odd b c d 2
  norm_num at h
  rw [h]
  ring

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

lemma n6 (hb : b ≠ 0) : normEDS b c d 6 = b * c * (normEDS b c d 5 - d ^ 2) := by
  have h := normEDS_even b c d 3
  norm_num at h
  apply mul_right_cancel₀ hb
  linear_combination h

lemma rel5 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 5)) * normEDS b c d (m + (j - 5))
      - (d * b ^ 4 - c ^ 3) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd320.main R b c d (m + j)
  rw [show m + j + 5 = m + (j + 5) by ring, show m + j - 5 = m + (j - 5) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n6 b c d hb, normEDS_four, n5 b c d] at h
  linear_combination h

omit [IsDomain R] in
lemma n7 : normEDS b c d 7 = c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3 := by
  have h := normEDS_odd b c d 3
  norm_num at h
  rw [h, n5 b c d]
  ring

lemma n8 (hb : b ≠ 0) :
    normEDS b c d 8 = c ^ 2 * d * normEDS b c d 6 - d * b * normEDS b c d 5 ^ 2 := by
  have h := normEDS_even b c d 4
  norm_num at h
  apply mul_right_cancel₀ hb
  linear_combination h

lemma rel6 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 6)) * normEDS b c d (m + (j - 6))
      - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd328.main R b c d (m + j)
  rw [show m + j + 6 = m + (j + 6) by ring, show m + j - 6 = m + (j - 6) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n6 b c d hb, n7 b c d, n5 b c d] at h
  linear_combination h

lemma gen (hb : b ≠ 0) (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (m : ℤ) :
    normEDS b c d (m + 7) * normEDS b c d (m - 7)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 7 ^ 2
      + normEDS b c d 8 * normEDS b c d 6 * normEDS b c d m ^ 2 = 0 := by
  have hpoly : normEDS b c d (m + 7) * normEDS b c d (m - 7)
      - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2)
        * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * normEDS b c d m ^ 2 = 0 := by
    by_cases hm : m = 3 ∨ m = 4
    · have h := cert_b b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j) (fun j => rel6 b c d hb m j)
      rw [add_zero, show m + -7 = m - 7 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m + 1) * normEDS b c d (m + 2) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
    · have h := cert_a b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j) (fun j => rel6 b c d hb m j)
      rw [add_zero, show m + -4 = m - 4 by ring, show m + -3 = m - 3 by ring,
        show m + -7 = m - 7 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m - 4) * normEDS b c d (m - 3) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
  rw [n8 b c d hb, n7 b c d, n6 b c d hb, n5 b c d]
  linear_combination hpoly

end Gen

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 7) * normEDS b c d (m - 7)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 7 ^ 2
      + normEDS b c d 8 * normEDS b c d 6 * normEDS b c d m ^ 2 = 0 := by
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

end N7

lemma cert_a {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - (d * b) ^ 2 * X (j + 1) * X (j - 1) + (d * b ^ 4 - c ^ 3) * c * X j ^ 2 = 0)
    (h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - (d * b ^ 4 - c ^ 3) ^ 2 * X (j + 1) * X (j - 1) + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X j ^ 2 = 0)
    (h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * X j ^ 2 = 0)
    (_h7 : ∀ j : ℤ, X (j + 7) * X (j - 7) - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X j ^ 2 = 0) :
    X (-4) * X (-3) * (X 8 * X (-8)
      - (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2 * X 1 * X (-1)
      + ((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * X 0 ^ 2) = 0 := by
  have e2_m3 := h2 (-3)
  have e2_m2 := h2 (-2)
  have e2_m1 := h2 (-1)
  have e2_0 := h2 0
  have e2_1 := h2 1
  have e3_m2 := h3 (-2)
  have e3_m1 := h3 (-1)
  have e3_0 := h3 0
  have e3_2 := h3 2
  have e4_0 := h4 0
  have e4_1 := h4 1
  have e5_m3 := h5 (-3)
  have e6_m2 := h6 (-2)
  have e6_2 := h6 2
  norm_num at e2_m3 e2_m2 e2_m1 e2_0 e2_1 e3_m2 e3_m1 e3_0 e3_2 e4_0 e4_1 e5_m3 e6_m2 e6_2
  linear_combination
    (b ^ 2 * c ^ 9 * d ^ 2 * X (-4) * X 3) * e2_m3
    + (-2) * (b ^ 6 * c ^ 6 * d ^ 3 * X (-4) * X 3) * e2_m3
    + (b ^ 10 * c ^ 3 * d ^ 4 * X (-4) * X 3) * e2_m3
    - (b ^ 2 * c ^ 6 * d ^ 4 * X (-4) * X 3) * e2_m3
    + (2) * (b ^ 6 * c ^ 3 * d ^ 5 * X (-4) * X 3) * e2_m3
    - (b ^ 10 * d ^ 6 * X (-4) * X 3) * e2_m3
    - (b ^ 2 * c ^ 12 * d * X (-3) * X 2) * e2_m3
    + (2) * (b ^ 6 * c ^ 9 * d ^ 2 * X (-3) * X 2) * e2_m3
    - (b ^ 10 * c ^ 6 * d ^ 3 * X (-3) * X 2) * e2_m3
    - (b ^ 2 * c ^ 9 * d ^ 3 * X (-3) * X 2) * e2_m3
    + (b ^ 6 * c ^ 6 * d ^ 4 * X (-3) * X 2) * e2_m3
    - (b ^ 2 * c ^ 13 * d * X (-2) * X 1) * e2_m3
    + (3) * (b ^ 6 * c ^ 10 * d ^ 2 * X (-2) * X 1) * e2_m3
    + (-3) * (b ^ 10 * c ^ 7 * d ^ 3 * X (-2) * X 1) * e2_m3
    + (b ^ 2 * c ^ 10 * d ^ 3 * X (-2) * X 1) * e2_m3
    + (b ^ 14 * c ^ 4 * d ^ 4 * X (-2) * X 1) * e2_m3
    + (-3) * (b ^ 6 * c ^ 7 * d ^ 4 * X (-2) * X 1) * e2_m3
    + (3) * (b ^ 10 * c ^ 4 * d ^ 5 * X (-2) * X 1) * e2_m3
    - (b ^ 14 * c * d ^ 6 * X (-2) * X 1) * e2_m3
    + (-2) * (b ^ 2 * c ^ 12 * d ^ 2 * X (-1) * X 0) * e2_m3
    + (5) * (b ^ 6 * c ^ 9 * d ^ 3 * X (-1) * X 0) * e2_m3
    + (-4) * (b ^ 10 * c ^ 6 * d ^ 4 * X (-1) * X 0) * e2_m3
    + (b ^ 14 * c ^ 3 * d ^ 5 * X (-1) * X 0) * e2_m3
    + (-2) * (b ^ 6 * c ^ 6 * d ^ 5 * X (-1) * X 0) * e2_m3
    + (3) * (b ^ 10 * c ^ 3 * d ^ 6 * X (-1) * X 0) * e2_m3
    - (b ^ 14 * d ^ 7 * X (-1) * X 0) * e2_m3
    - (c ^ 12 * d * X (-5) * X 2) * e2_m2
    + (2) * (b ^ 4 * c ^ 9 * d ^ 2 * X (-5) * X 2) * e2_m2
    - (b ^ 8 * c ^ 6 * d ^ 3 * X (-5) * X 2) * e2_m2
    - (c ^ 9 * d ^ 3 * X (-5) * X 2) * e2_m2
    + (b ^ 4 * c ^ 6 * d ^ 4 * X (-5) * X 2) * e2_m2
    - (c ^ 13 * d ^ 2 * X (-3) * X 0) * e2_m2
    + (3) * (b ^ 4 * c ^ 10 * d ^ 3 * X (-3) * X 0) * e2_m2
    + (-3) * (b ^ 8 * c ^ 7 * d ^ 4 * X (-3) * X 0) * e2_m2
    - (c ^ 10 * d ^ 4 * X (-3) * X 0) * e2_m2
    + (b ^ 12 * c ^ 4 * d ^ 5 * X (-3) * X 0) * e2_m2
    + (2) * (b ^ 8 * c ^ 4 * d ^ 6 * X (-3) * X 0) * e2_m2
    - (b ^ 12 * c * d ^ 7 * X (-3) * X 0) * e2_m2
    + (-2) * (b ^ 4 * c ^ 12 * d ^ 2 * X (-2) * X (-1)) * e2_m2
    + (5) * (b ^ 8 * c ^ 9 * d ^ 3 * X (-2) * X (-1)) * e2_m2
    + (-4) * (b ^ 12 * c ^ 6 * d ^ 4 * X (-2) * X (-1)) * e2_m2
    + (b ^ 16 * c ^ 3 * d ^ 5 * X (-2) * X (-1)) * e2_m2
    + (-2) * (b ^ 8 * c ^ 6 * d ^ 5 * X (-2) * X (-1)) * e2_m2
    + (3) * (b ^ 12 * c ^ 3 * d ^ 6 * X (-2) * X (-1)) * e2_m2
    - (b ^ 16 * d ^ 7 * X (-2) * X (-1)) * e2_m2
    - (b ^ 2 * c ^ 5 * d ^ 2 * X (-8) * X 3) * e2_m1
    + (b ^ 2 * c ^ 2 * d ^ 4 * X (-8) * X 3) * e2_m1
    + (b ^ 2 * c ^ 11 * d ^ 2 * X (-5) * X 0) * e2_m1
    + (-2) * (b ^ 6 * c ^ 8 * d ^ 3 * X (-5) * X 0) * e2_m1
    + (b ^ 10 * c ^ 5 * d ^ 4 * X (-5) * X 0) * e2_m1
    - (b ^ 2 * c ^ 8 * d ^ 4 * X (-5) * X 0) * e2_m1
    + (2) * (b ^ 6 * c ^ 5 * d ^ 5 * X (-5) * X 0) * e2_m1
    - (b ^ 10 * c ^ 2 * d ^ 6 * X (-5) * X 0) * e2_m1
    + (2) * (b ^ 2 * c ^ 14 * d * X (-3) * X (-2)) * e2_m1
    + (-5) * (b ^ 6 * c ^ 11 * d ^ 2 * X (-3) * X (-2)) * e2_m1
    + (4) * (b ^ 10 * c ^ 8 * d ^ 3 * X (-3) * X (-2)) * e2_m1
    + (b ^ 2 * c ^ 11 * d ^ 3 * X (-3) * X (-2)) * e2_m1
    - (b ^ 14 * c ^ 5 * d ^ 4 * X (-3) * X (-2)) * e2_m1
    + (b ^ 6 * c ^ 8 * d ^ 4 * X (-3) * X (-2)) * e2_m1
    + (-3) * (b ^ 10 * c ^ 5 * d ^ 5 * X (-3) * X (-2)) * e2_m1
    + (b ^ 2 * c ^ 8 * d ^ 5 * X (-3) * X (-2)) * e2_m1
    + (b ^ 14 * c ^ 2 * d ^ 6 * X (-3) * X (-2)) * e2_m1
    - (c ^ 10 * X (-8) * X 1) * e2_0
    + (b ^ 4 * c ^ 7 * d * X (-8) * X 1) * e2_0
    - (c ^ 7 * d ^ 2 * X (-8) * X 1) * e2_0
    + (c ^ 13 * d * X (-5) * X (-2)) * e2_0
    + (-2) * (b ^ 4 * c ^ 10 * d ^ 2 * X (-5) * X (-2)) * e2_0
    + (b ^ 8 * c ^ 7 * d ^ 3 * X (-5) * X (-2)) * e2_0
    + (c ^ 10 * d ^ 3 * X (-5) * X (-2)) * e2_0
    - (b ^ 4 * c ^ 7 * d ^ 4 * X (-5) * X (-2)) * e2_0
    - (c ^ 15 * X (-4) * X (-3)) * e2_0
    + (4) * (b ^ 4 * c ^ 12 * d * X (-4) * X (-3)) * e2_0
    + (-6) * (b ^ 8 * c ^ 9 * d ^ 2 * X (-4) * X (-3)) * e2_0
    + (c ^ 12 * d ^ 2 * X (-4) * X (-3)) * e2_0
    + (4) * (b ^ 12 * c ^ 6 * d ^ 3 * X (-4) * X (-3)) * e2_0
    + (-2) * (b ^ 4 * c ^ 9 * d ^ 3 * X (-4) * X (-3)) * e2_0
    - (b ^ 16 * c ^ 3 * d ^ 4 * X (-4) * X (-3)) * e2_0
    + (3) * (b ^ 8 * c ^ 6 * d ^ 4 * X (-4) * X (-3)) * e2_0
    + (c ^ 9 * d ^ 4 * X (-4) * X (-3)) * e2_0
    + (-3) * (b ^ 12 * c ^ 3 * d ^ 5 * X (-4) * X (-3)) * e2_0
    + (b ^ 16 * d ^ 6 * X (-4) * X (-3)) * e2_0
    + (b ^ 2 * c ^ 6 * d ^ 2 * X (-8) * X (-1)) * e2_1
    - (b ^ 6 * c ^ 3 * d ^ 3 * X (-8) * X (-1)) * e2_1
    - (b ^ 2 * c ^ 3 * d ^ 4 * X (-8) * X (-1)) * e2_1
    + (b ^ 6 * d ^ 5 * X (-8) * X (-1)) * e2_1
    - (b ^ 2 * c ^ 9 * d ^ 2 * X (-5) * X (-4)) * e2_1
    + (2) * (b ^ 6 * c ^ 6 * d ^ 3 * X (-5) * X (-4)) * e2_1
    - (b ^ 10 * c ^ 3 * d ^ 4 * X (-5) * X (-4)) * e2_1
    + (b ^ 2 * c ^ 6 * d ^ 4 * X (-5) * X (-4)) * e2_1
    + (-2) * (b ^ 6 * c ^ 3 * d ^ 5 * X (-5) * X (-4)) * e2_1
    + (b ^ 10 * d ^ 6 * X (-5) * X (-4)) * e2_1
    + (b ^ 2 * c ^ 10 * d ^ 2 * X (-4) * X 1) * e3_m2
    + (-2) * (b ^ 6 * c ^ 7 * d ^ 3 * X (-4) * X 1) * e3_m2
    + (b ^ 10 * c ^ 4 * d ^ 4 * X (-4) * X 1) * e3_m2
    - (b ^ 2 * c ^ 7 * d ^ 4 * X (-4) * X 1) * e3_m2
    + (2) * (b ^ 6 * c ^ 4 * d ^ 5 * X (-4) * X 1) * e3_m2
    - (b ^ 10 * c * d ^ 6 * X (-4) * X 1) * e3_m2
    - (b ^ 2 * c ^ 11 * d ^ 2 * X (-3) * X 0) * e3_m2
    + (2) * (b ^ 6 * c ^ 8 * d ^ 3 * X (-3) * X 0) * e3_m2
    - (b ^ 10 * c ^ 5 * d ^ 4 * X (-3) * X 0) * e3_m2
    + (b ^ 2 * c ^ 8 * d ^ 4 * X (-3) * X 0) * e3_m2
    + (-2) * (b ^ 6 * c ^ 5 * d ^ 5 * X (-3) * X 0) * e3_m2
    + (b ^ 10 * c ^ 2 * d ^ 6 * X (-3) * X 0) * e3_m2
    + (2) * (b ^ 2 * c ^ 13 * d * X (-2) * X (-1)) * e3_m2
    + (-5) * (b ^ 6 * c ^ 10 * d ^ 2 * X (-2) * X (-1)) * e3_m2
    + (4) * (b ^ 10 * c ^ 7 * d ^ 3 * X (-2) * X (-1)) * e3_m2
    - (b ^ 14 * c ^ 4 * d ^ 4 * X (-2) * X (-1)) * e3_m2
    + (2) * (b ^ 6 * c ^ 7 * d ^ 4 * X (-2) * X (-1)) * e3_m2
    + (-3) * (b ^ 10 * c ^ 4 * d ^ 5 * X (-2) * X (-1)) * e3_m2
    + (b ^ 14 * c * d ^ 6 * X (-2) * X (-1)) * e3_m2
    + (b ^ 4 * c ^ 3 * d ^ 2 * X (-8) * X 3) * e3_m1
    - (b ^ 4 * d ^ 4 * X (-8) * X 3) * e3_m1
    + (c ^ 12 * d * X (-5) * X 0) * e3_m1
    + (-3) * (b ^ 4 * c ^ 9 * d ^ 2 * X (-5) * X 0) * e3_m1
    + (3) * (b ^ 8 * c ^ 6 * d ^ 3 * X (-5) * X 0) * e3_m1
    + (c ^ 9 * d ^ 3 * X (-5) * X 0) * e3_m1
    - (b ^ 12 * c ^ 3 * d ^ 4 * X (-5) * X 0) * e3_m1
    + (-2) * (b ^ 8 * c ^ 3 * d ^ 5 * X (-5) * X 0) * e3_m1
    + (b ^ 12 * d ^ 6 * X (-5) * X 0) * e3_m1
    + (-2) * (b ^ 4 * c ^ 12 * d * X (-3) * X (-2)) * e3_m1
    + (5) * (b ^ 8 * c ^ 9 * d ^ 2 * X (-3) * X (-2)) * e3_m1
    - (c ^ 12 * d ^ 2 * X (-3) * X (-2)) * e3_m1
    + (-4) * (b ^ 12 * c ^ 6 * d ^ 3 * X (-3) * X (-2)) * e3_m1
    + (b ^ 4 * c ^ 9 * d ^ 3 * X (-3) * X (-2)) * e3_m1
    + (b ^ 16 * c ^ 3 * d ^ 4 * X (-3) * X (-2)) * e3_m1
    + (-2) * (b ^ 8 * c ^ 6 * d ^ 4 * X (-3) * X (-2)) * e3_m1
    - (c ^ 9 * d ^ 4 * X (-3) * X (-2)) * e3_m1
    + (3) * (b ^ 12 * c ^ 3 * d ^ 5 * X (-3) * X (-2)) * e3_m1
    - (b ^ 16 * d ^ 6 * X (-3) * X (-2)) * e3_m1
    + (2) * (b ^ 2 * c ^ 8 * X (-8) * X 1) * e3_0
    + (-3) * (b ^ 6 * c ^ 5 * d * X (-8) * X 1) * e3_0
    + (b ^ 10 * c ^ 2 * d ^ 2 * X (-8) * X 1) * e3_0
    + (2) * (b ^ 2 * c ^ 5 * d ^ 2 * X (-8) * X 1) * e3_0
    - (b ^ 6 * c ^ 2 * d ^ 3 * X (-8) * X 1) * e3_0
    - (b ^ 2 * c ^ 10 * d ^ 2 * X (-4) * X (-3)) * e3_0
    + (b ^ 6 * c ^ 7 * d ^ 3 * X (-4) * X (-3)) * e3_0
    + (b ^ 2 * c ^ 7 * d ^ 4 * X (-4) * X (-3)) * e3_0
    + (-2) * (b ^ 6 * c ^ 4 * d ^ 5 * X (-4) * X (-3)) * e3_0
    + (b ^ 6 * c * d ^ 7 * X (-4) * X (-3)) * e3_0
    + (b ^ 2 * c ^ 6 * X (-8) * X (-3)) * e3_2
    - (b ^ 6 * c ^ 3 * d * X (-8) * X (-3)) * e3_2
    - (b ^ 2 * c ^ 3 * d ^ 2 * X (-8) * X (-3)) * e3_2
    + (b ^ 6 * d ^ 3 * X (-8) * X (-3)) * e3_2
    - (c ^ 7 * X (-8) * X 1) * e4_0
    + (2) * (b ^ 4 * c ^ 4 * d * X (-8) * X 1) * e4_0
    - (b ^ 8 * c * d ^ 2 * X (-8) * X 1) * e4_0
    - (c ^ 4 * d ^ 2 * X (-8) * X 1) * e4_0
    + (b ^ 4 * c * d ^ 3 * X (-8) * X 1) * e4_0
    - (b ^ 2 * c ^ 6 * X (-8) * X (-1)) * e4_1
    + (b ^ 6 * c ^ 3 * d * X (-8) * X (-1)) * e4_1
    + (b ^ 2 * c ^ 3 * d ^ 2 * X (-8) * X (-1)) * e4_1
    - (b ^ 6 * d ^ 3 * X (-8) * X (-1)) * e4_1
    - (b ^ 4 * c ^ 3 * d ^ 2 * X (-4) * X 3) * e5_m3
    + (b ^ 4 * d ^ 4 * X (-4) * X 3) * e5_m3
    - (c ^ 9 * X (-3) * X 2) * e5_m3
    + (b ^ 4 * c ^ 6 * d * X (-3) * X 2) * e5_m3
    + (c ^ 10 * X (-2) * X 1) * e5_m3
    - (b ^ 4 * c ^ 7 * d * X (-2) * X 1) * e5_m3
    + (c ^ 7 * d ^ 2 * X (-2) * X 1) * e5_m3
    + (c ^ 7 * X (-4) * X 1) * e6_m2
    + (-2) * (b ^ 4 * c ^ 4 * d * X (-4) * X 1) * e6_m2
    + (b ^ 8 * c * d ^ 2 * X (-4) * X 1) * e6_m2
    + (c ^ 4 * d ^ 2 * X (-4) * X 1) * e6_m2
    - (b ^ 4 * c * d ^ 3 * X (-4) * X 1) * e6_m2
    + (X (-8) * X (-3)) * e6_2

lemma cert_b {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - b ^ 2 * X (j + 1) * X (j - 1) + c * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - c ^ 2 * X (j + 1) * X (j - 1) + d * b * b * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - (d * b) ^ 2 * X (j + 1) * X (j - 1) + (d * b ^ 4 - c ^ 3) * c * X j ^ 2 = 0)
    (h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - (d * b ^ 4 - c ^ 3) ^ 2 * X (j + 1) * X (j - 1) + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * X j ^ 2 = 0)
    (h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * X j ^ 2 = 0)
    (_h7 : ∀ j : ℤ, X (j + 7) * X (j - 7) - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * X (j + 1) * X (j - 1) + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X j ^ 2 = 0) :
    X 1 * X 2 * (X 8 * X (-8)
      - (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2 * X 1 * X (-1)
      + ((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * X 0 ^ 2) = 0 := by
  have e2_m3 := h2 (-3)
  have e2_m2 := h2 (-2)
  have e2_m1 := h2 (-1)
  have e2_0 := h2 0
  have e2_1 := h2 1
  have e2_2 := h2 2
  have e2_3 := h2 3
  have e3_m2 := h3 (-2)
  have e3_m1 := h3 (-1)
  have e3_0 := h3 0
  have e3_1 := h3 1
  have e4_0 := h4 0
  have e5_m3 := h5 (-3)
  have e5_3 := h5 3
  have e6_2 := h6 2
  norm_num at e2_m3 e2_m2 e2_m1 e2_0 e2_1 e2_2 e2_3 e3_m2 e3_m1 e3_0 e3_1 e4_0 e5_m3 e5_3 e6_2
  linear_combination
    (b ^ 2 * c ^ 3 * d * X 1 * X 8) * e2_m3
    - (b ^ 6 * d ^ 2 * X 1 * X 8) * e2_m3
    + (b ^ 2 * d ^ 3 * X 1 * X 8) * e2_m3
    - (c ^ 8 * d ^ 2 * X 2 * X 5) * e2_m2
    + (2) * (b ^ 4 * c ^ 5 * d ^ 3 * X 2 * X 5) * e2_m2
    - (b ^ 8 * c ^ 2 * d ^ 4 * X 2 * X 5) * e2_m2
    - (c ^ 5 * d ^ 4 * X 2 * X 5) * e2_m2
    + (b ^ 4 * c ^ 2 * d ^ 5 * X 2 * X 5) * e2_m2
    + (c ^ 10 * d * X 3 * X 4) * e2_m2
    + (-2) * (b ^ 4 * c ^ 7 * d ^ 2 * X 3 * X 4) * e2_m2
    + (b ^ 8 * c ^ 4 * d ^ 3 * X 3 * X 4) * e2_m2
    + (c ^ 7 * d ^ 3 * X 3 * X 4) * e2_m2
    - (b ^ 8 * c * d ^ 5 * X 3 * X 4) * e2_m2
    + (b ^ 4 * c * d ^ 6 * X 3 * X 4) * e2_m2
    - (b ^ 2 * c ^ 7 * d ^ 3 * X 0 * X 5) * e2_m1
    + (2) * (b ^ 6 * c ^ 4 * d ^ 4 * X 0 * X 5) * e2_m1
    - (b ^ 10 * c * d ^ 5 * X 0 * X 5) * e2_m1
    - (b ^ 2 * c ^ 4 * d ^ 5 * X 0 * X 5) * e2_m1
    + (b ^ 6 * c * d ^ 6 * X 0 * X 5) * e2_m1
    + (b ^ 2 * c ^ 8 * d ^ 3 * X 1 * X 4) * e2_m1
    + (-2) * (b ^ 6 * c ^ 5 * d ^ 4 * X 1 * X 4) * e2_m1
    + (b ^ 10 * c ^ 2 * d ^ 5 * X 1 * X 4) * e2_m1
    + (b ^ 2 * c ^ 5 * d ^ 5 * X 1 * X 4) * e2_m1
    - (b ^ 6 * c ^ 2 * d ^ 6 * X 1 * X 4) * e2_m1
    - (b ^ 6 * c ^ 7 * d ^ 3 * X 2 * X 3) * e2_m1
    + (2) * (b ^ 10 * c ^ 4 * d ^ 4 * X 2 * X 3) * e2_m1
    - (b ^ 14 * c * d ^ 5 * X 2 * X 3) * e2_m1
    + (-2) * (b ^ 6 * c ^ 4 * d ^ 5 * X 2 * X 3) * e2_m1
    + (2) * (b ^ 10 * c * d ^ 6 * X 2 * X 3) * e2_m1
    - (b ^ 6 * c * d ^ 7 * X 2 * X 3) * e2_m1
    + (c ^ 3 * d * X (-5) * X 8) * e2_0
    - (b ^ 4 * d ^ 2 * X (-5) * X 8) * e2_0
    + (c ^ 9 * d ^ 2 * X (-2) * X 5) * e2_0
    + (-3) * (b ^ 4 * c ^ 6 * d ^ 3 * X (-2) * X 5) * e2_0
    + (3) * (b ^ 8 * c ^ 3 * d ^ 4 * X (-2) * X 5) * e2_0
    + (c ^ 6 * d ^ 4 * X (-2) * X 5) * e2_0
    - (b ^ 12 * d ^ 5 * X (-2) * X 5) * e2_0
    + (-2) * (b ^ 4 * c ^ 3 * d ^ 5 * X (-2) * X 5) * e2_0
    + (b ^ 8 * d ^ 6 * X (-2) * X 5) * e2_0
    + (c ^ 12 * d * X (-1) * X 4) * e2_0
    + (-3) * (b ^ 4 * c ^ 9 * d ^ 2 * X (-1) * X 4) * e2_0
    + (3) * (b ^ 8 * c ^ 6 * d ^ 3 * X (-1) * X 4) * e2_0
    + (c ^ 9 * d ^ 3 * X (-1) * X 4) * e2_0
    - (b ^ 12 * c ^ 3 * d ^ 4 * X (-1) * X 4) * e2_0
    - (b ^ 4 * c ^ 6 * d ^ 4 * X (-1) * X 4) * e2_0
    - (b ^ 8 * c ^ 3 * d ^ 5 * X (-1) * X 4) * e2_0
    + (c ^ 6 * d ^ 5 * X (-1) * X 4) * e2_0
    + (b ^ 12 * d ^ 6 * X (-1) * X 4) * e2_0
    - (b ^ 4 * c ^ 3 * d ^ 6 * X (-1) * X 4) * e2_0
    + (b ^ 4 * c ^ 7 * d ^ 4 * X 0 * X 3) * e2_0
    + (-2) * (b ^ 8 * c ^ 4 * d ^ 5 * X 0 * X 3) * e2_0
    + (b ^ 12 * c * d ^ 6 * X 0 * X 3) * e2_0
    + (b ^ 4 * c ^ 4 * d ^ 6 * X 0 * X 3) * e2_0
    - (b ^ 8 * c * d ^ 7 * X 0 * X 3) * e2_0
    + (2) * (c ^ 12 * d ^ 2 * X 1 * X 2) * e2_0
    + (-6) * (b ^ 4 * c ^ 9 * d ^ 3 * X 1 * X 2) * e2_0
    + (6) * (b ^ 8 * c ^ 6 * d ^ 4 * X 1 * X 2) * e2_0
    + (2) * (c ^ 9 * d ^ 4 * X 1 * X 2) * e2_0
    + (-2) * (b ^ 12 * c ^ 3 * d ^ 5 * X 1 * X 2) * e2_0
    + (-4) * (b ^ 4 * c ^ 6 * d ^ 5 * X 1 * X 2) * e2_0
    + (2) * (b ^ 8 * c ^ 3 * d ^ 6 * X 1 * X 2) * e2_0
    - (b ^ 2 * c ^ 7 * d ^ 3 * X (-3) * X 4) * e2_1
    + (2) * (b ^ 6 * c ^ 4 * d ^ 4 * X (-3) * X 4) * e2_1
    - (b ^ 10 * c * d ^ 5 * X (-3) * X 4) * e2_1
    - (b ^ 2 * c ^ 4 * d ^ 5 * X (-3) * X 4) * e2_1
    + (b ^ 6 * c * d ^ 6 * X (-3) * X 4) * e2_1
    - (b ^ 2 * c ^ 10 * d ^ 2 * X (-2) * X 3) * e2_1
    + (3) * (b ^ 6 * c ^ 7 * d ^ 3 * X (-2) * X 3) * e2_1
    + (-3) * (b ^ 10 * c ^ 4 * d ^ 4 * X (-2) * X 3) * e2_1
    - (b ^ 2 * c ^ 7 * d ^ 4 * X (-2) * X 3) * e2_1
    + (b ^ 14 * c * d ^ 5 * X (-2) * X 3) * e2_1
    + (2) * (b ^ 6 * c ^ 4 * d ^ 5 * X (-2) * X 3) * e2_1
    - (b ^ 10 * c * d ^ 6 * X (-2) * X 3) * e2_1
    - (b ^ 2 * c ^ 11 * d ^ 2 * X (-1) * X 2) * e2_1
    + (3) * (b ^ 6 * c ^ 8 * d ^ 3 * X (-1) * X 2) * e2_1
    + (-3) * (b ^ 10 * c ^ 5 * d ^ 4 * X (-1) * X 2) * e2_1
    - (b ^ 2 * c ^ 8 * d ^ 4 * X (-1) * X 2) * e2_1
    + (b ^ 14 * c ^ 2 * d ^ 5 * X (-1) * X 2) * e2_1
    + (2) * (b ^ 6 * c ^ 5 * d ^ 5 * X (-1) * X 2) * e2_1
    - (b ^ 10 * c ^ 2 * d ^ 6 * X (-1) * X 2) * e2_1
    - (b ^ 2 * c ^ 13 * d * X 0 * X 1) * e2_1
    + (3) * (b ^ 6 * c ^ 10 * d ^ 2 * X 0 * X 1) * e2_1
    + (-3) * (b ^ 10 * c ^ 7 * d ^ 3 * X 0 * X 1) * e2_1
    + (-2) * (b ^ 2 * c ^ 10 * d ^ 3 * X 0 * X 1) * e2_1
    + (b ^ 14 * c ^ 4 * d ^ 4 * X 0 * X 1) * e2_1
    + (4) * (b ^ 6 * c ^ 7 * d ^ 4 * X 0 * X 1) * e2_1
    + (-2) * (b ^ 10 * c ^ 4 * d ^ 5 * X 0 * X 1) * e2_1
    + (-2) * (b ^ 2 * c ^ 7 * d ^ 5 * X 0 * X 1) * e2_1
    + (3) * (b ^ 6 * c ^ 4 * d ^ 6 * X 0 * X 1) * e2_1
    - (b ^ 10 * c * d ^ 7 * X 0 * X 1) * e2_1
    - (c ^ 10 * d * X (-4) * X 3) * e2_2
    + (2) * (b ^ 4 * c ^ 7 * d ^ 2 * X (-4) * X 3) * e2_2
    - (b ^ 8 * c ^ 4 * d ^ 3 * X (-4) * X 3) * e2_2
    - (c ^ 7 * d ^ 3 * X (-4) * X 3) * e2_2
    + (b ^ 8 * c * d ^ 5 * X (-4) * X 3) * e2_2
    - (b ^ 4 * c * d ^ 6 * X (-4) * X 3) * e2_2
    + (-2) * (c ^ 11 * d ^ 2 * X (-2) * X 1) * e2_2
    + (6) * (b ^ 4 * c ^ 8 * d ^ 3 * X (-2) * X 1) * e2_2
    + (-6) * (b ^ 8 * c ^ 5 * d ^ 4 * X (-2) * X 1) * e2_2
    + (-2) * (c ^ 8 * d ^ 4 * X (-2) * X 1) * e2_2
    + (2) * (b ^ 12 * c ^ 2 * d ^ 5 * X (-2) * X 1) * e2_2
    + (4) * (b ^ 4 * c ^ 5 * d ^ 5 * X (-2) * X 1) * e2_2
    + (-2) * (b ^ 8 * c ^ 2 * d ^ 6 * X (-2) * X 1) * e2_2
    - (c ^ 13 * d * X (-1) * X 0) * e2_2
    + (3) * (b ^ 4 * c ^ 10 * d ^ 2 * X (-1) * X 0) * e2_2
    + (-3) * (b ^ 8 * c ^ 7 * d ^ 3 * X (-1) * X 0) * e2_2
    - (c ^ 10 * d ^ 3 * X (-1) * X 0) * e2_2
    + (b ^ 12 * c ^ 4 * d ^ 4 * X (-1) * X 0) * e2_2
    + (b ^ 4 * c ^ 7 * d ^ 4 * X (-1) * X 0) * e2_2
    + (b ^ 8 * c ^ 4 * d ^ 5 * X (-1) * X 0) * e2_2
    - (c ^ 7 * d ^ 5 * X (-1) * X 0) * e2_2
    - (b ^ 12 * c * d ^ 6 * X (-1) * X 0) * e2_2
    + (b ^ 4 * c ^ 4 * d ^ 6 * X (-1) * X 0) * e2_2
    - (b ^ 2 * c ^ 6 * d ^ 2 * X (-5) * X 2) * e2_3
    + (2) * (b ^ 6 * c ^ 3 * d ^ 3 * X (-5) * X 2) * e2_3
    - (b ^ 10 * d ^ 4 * X (-5) * X 2) * e2_3
    - (b ^ 2 * c ^ 3 * d ^ 4 * X (-5) * X 2) * e2_3
    + (b ^ 6 * d ^ 5 * X (-5) * X 2) * e2_3
    + (b ^ 2 * c ^ 7 * d ^ 3 * X (-3) * X 0) * e2_3
    + (-2) * (b ^ 6 * c ^ 4 * d ^ 4 * X (-3) * X 0) * e2_3
    + (b ^ 10 * c * d ^ 5 * X (-3) * X 0) * e2_3
    + (b ^ 2 * c ^ 4 * d ^ 5 * X (-3) * X 0) * e2_3
    - (b ^ 6 * c * d ^ 6 * X (-3) * X 0) * e2_3
    + (b ^ 2 * c ^ 9 * d ^ 2 * X (-2) * X (-1)) * e2_3
    + (-3) * (b ^ 6 * c ^ 6 * d ^ 3 * X (-2) * X (-1)) * e2_3
    + (3) * (b ^ 10 * c ^ 3 * d ^ 4 * X (-2) * X (-1)) * e2_3
    + (b ^ 2 * c ^ 6 * d ^ 4 * X (-2) * X (-1)) * e2_3
    - (b ^ 14 * d ^ 5 * X (-2) * X (-1)) * e2_3
    + (-2) * (b ^ 6 * c ^ 3 * d ^ 5 * X (-2) * X (-1)) * e2_3
    + (b ^ 10 * d ^ 6 * X (-2) * X (-1)) * e2_3
    + (b ^ 2 * c ^ 6 * d ^ 2 * X 2 * X 5) * e3_m2
    + (-2) * (b ^ 6 * c ^ 3 * d ^ 3 * X 2 * X 5) * e3_m2
    + (b ^ 10 * d ^ 4 * X 2 * X 5) * e3_m2
    + (b ^ 2 * c ^ 3 * d ^ 4 * X 2 * X 5) * e3_m2
    - (b ^ 6 * d ^ 5 * X 2 * X 5) * e3_m2
    - (b ^ 2 * c ^ 8 * d * X 3 * X 4) * e3_m2
    + (2) * (b ^ 6 * c ^ 5 * d ^ 2 * X 3 * X 4) * e3_m2
    - (b ^ 10 * c ^ 2 * d ^ 3 * X 3 * X 4) * e3_m2
    + (-2) * (b ^ 2 * c ^ 5 * d ^ 3 * X 3 * X 4) * e3_m2
    + (2) * (b ^ 6 * c ^ 2 * d ^ 4 * X 3 * X 4) * e3_m2
    - (b ^ 2 * c ^ 2 * d ^ 5 * X 3 * X 4) * e3_m2
    + (c ^ 8 * d ^ 2 * X 0 * X 5) * e3_m1
    + (-2) * (b ^ 4 * c ^ 5 * d ^ 3 * X 0 * X 5) * e3_m1
    + (b ^ 8 * c ^ 2 * d ^ 4 * X 0 * X 5) * e3_m1
    + (c ^ 5 * d ^ 4 * X 0 * X 5) * e3_m1
    - (b ^ 4 * c ^ 2 * d ^ 5 * X 0 * X 5) * e3_m1
    + (c ^ 12 * X 1 * X 4) * e3_m1
    + (-3) * (b ^ 4 * c ^ 9 * d * X 1 * X 4) * e3_m1
    + (3) * (b ^ 8 * c ^ 6 * d ^ 2 * X 1 * X 4) * e3_m1
    - (b ^ 12 * c ^ 3 * d ^ 3 * X 1 * X 4) * e3_m1
    + (b ^ 4 * c ^ 6 * d ^ 3 * X 1 * X 4) * e3_m1
    + (-2) * (b ^ 8 * c ^ 3 * d ^ 4 * X 1 * X 4) * e3_m1
    + (b ^ 12 * d ^ 5 * X 1 * X 4) * e3_m1
    + (c ^ 11 * d * X 2 * X 3) * e3_m1
    + (-2) * (b ^ 4 * c ^ 8 * d ^ 2 * X 2 * X 3) * e3_m1
    + (b ^ 8 * c ^ 5 * d ^ 3 * X 2 * X 3) * e3_m1
    + (c ^ 8 * d ^ 3 * X 2 * X 3) * e3_m1
    - (b ^ 8 * c ^ 2 * d ^ 5 * X 2 * X 3) * e3_m1
    + (b ^ 4 * c ^ 2 * d ^ 6 * X 2 * X 3) * e3_m1
    - (b ^ 2 * c ^ 8 * d ^ 3 * X 0 * X 3) * e3_0
    + (2) * (b ^ 6 * c ^ 5 * d ^ 4 * X 0 * X 3) * e3_0
    - (b ^ 10 * c ^ 2 * d ^ 5 * X 0 * X 3) * e3_0
    - (b ^ 2 * c ^ 5 * d ^ 5 * X 0 * X 3) * e3_0
    + (b ^ 6 * c ^ 2 * d ^ 6 * X 0 * X 3) * e3_0
    + (b ^ 6 * c ^ 7 * d ^ 3 * X 1 * X 2) * e3_0
    + (-2) * (b ^ 10 * c ^ 4 * d ^ 4 * X 1 * X 2) * e3_0
    + (b ^ 14 * c * d ^ 5 * X 1 * X 2) * e3_0
    + (2) * (b ^ 6 * c ^ 4 * d ^ 5 * X 1 * X 2) * e3_0
    + (-2) * (b ^ 10 * c * d ^ 6 * X 1 * X 2) * e3_0
    + (b ^ 6 * c * d ^ 7 * X 1 * X 2) * e3_0
    - (c ^ 11 * d * X (-2) * X 3) * e3_1
    + (3) * (b ^ 4 * c ^ 8 * d ^ 2 * X (-2) * X 3) * e3_1
    + (-3) * (b ^ 8 * c ^ 5 * d ^ 3 * X (-2) * X 3) * e3_1
    - (c ^ 8 * d ^ 3 * X (-2) * X 3) * e3_1
    + (b ^ 12 * c ^ 2 * d ^ 4 * X (-2) * X 3) * e3_1
    + (2) * (b ^ 4 * c ^ 5 * d ^ 4 * X (-2) * X 3) * e3_1
    - (b ^ 8 * c ^ 2 * d ^ 5 * X (-2) * X 3) * e3_1
    - (c ^ 12 * d * X (-1) * X 2) * e3_1
    + (4) * (b ^ 4 * c ^ 9 * d ^ 2 * X (-1) * X 2) * e3_1
    + (-6) * (b ^ 8 * c ^ 6 * d ^ 3 * X (-1) * X 2) * e3_1
    - (c ^ 9 * d ^ 3 * X (-1) * X 2) * e3_1
    + (4) * (b ^ 12 * c ^ 3 * d ^ 4 * X (-1) * X 2) * e3_1
    + (2) * (b ^ 4 * c ^ 6 * d ^ 4 * X (-1) * X 2) * e3_1
    - (b ^ 16 * d ^ 5 * X (-1) * X 2) * e3_1
    - (b ^ 8 * c ^ 3 * d ^ 5 * X (-1) * X 2) * e3_1
    - (c ^ 6 * d ^ 5 * X (-1) * X 2) * e3_1
    + (b ^ 4 * c ^ 3 * d ^ 6 * X (-1) * X 2) * e3_1
    + (c ^ 14 * X 0 * X 1) * e3_1
    + (-3) * (b ^ 4 * c ^ 11 * d * X 0 * X 1) * e3_1
    + (3) * (b ^ 8 * c ^ 8 * d ^ 2 * X 0 * X 1) * e3_1
    + (2) * (c ^ 11 * d ^ 2 * X 0 * X 1) * e3_1
    - (b ^ 12 * c ^ 5 * d ^ 3 * X 0 * X 1) * e3_1
    + (-4) * (b ^ 4 * c ^ 8 * d ^ 3 * X 0 * X 1) * e3_1
    + (2) * (b ^ 8 * c ^ 5 * d ^ 4 * X 0 * X 1) * e3_1
    + (2) * (c ^ 8 * d ^ 4 * X 0 * X 1) * e3_1
    + (-3) * (b ^ 4 * c ^ 5 * d ^ 5 * X 0 * X 1) * e3_1
    + (b ^ 8 * c ^ 2 * d ^ 6 * X 0 * X 1) * e3_1
    + (d * X (-5) * X 8) * e4_0
    + (X 1 * X 8) * e5_m3
    - (c ^ 3 * d * X (-5) * X 2) * e5_3
    + (b ^ 4 * d ^ 2 * X (-5) * X 2) * e5_3
    + (c ^ 6 * X (-4) * X 1) * e5_3
    - (b ^ 4 * c ^ 3 * d * X (-4) * X 1) * e5_3
    + (b ^ 4 * d ^ 3 * X (-4) * X 1) * e5_3
    - (d * X (-5) * X 4) * e6_2


section Gen

variable {R : Type} [CommRing R] [IsDomain R] (b c d : R)

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
lemma n5 : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
  have h := normEDS_odd b c d 2
  norm_num at h
  rw [h]
  ring

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

lemma n6 (hb : b ≠ 0) : normEDS b c d 6 = b * c * (normEDS b c d 5 - d ^ 2) := by
  have h := normEDS_even b c d 3
  norm_num at h
  apply mul_right_cancel₀ hb
  linear_combination h

lemma rel5 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 5)) * normEDS b c d (m + (j - 5))
      - (d * b ^ 4 - c ^ 3) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd320.main R b c d (m + j)
  rw [show m + j + 5 = m + (j + 5) by ring, show m + j - 5 = m + (j - 5) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n6 b c d hb, normEDS_four, n5 b c d] at h
  linear_combination h

omit [IsDomain R] in
lemma n7 : normEDS b c d 7 = c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3 := by
  have h := normEDS_odd b c d 3
  norm_num at h
  rw [h, n5 b c d]
  ring

lemma n8 (hb : b ≠ 0) :
    normEDS b c d 8 = c ^ 2 * d * normEDS b c d 6 - d * b * normEDS b c d 5 ^ 2 := by
  have h := normEDS_even b c d 4
  norm_num at h
  apply mul_right_cancel₀ hb
  linear_combination h

lemma rel6 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 6)) * normEDS b c d (m + (j - 6))
      - (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd328.main R b c d (m + j)
  rw [show m + j + 6 = m + (j + 6) by ring, show m + j - 6 = m + (j - 6) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n6 b c d hb, n7 b c d, n5 b c d] at h
  linear_combination h

omit [IsDomain R] in
lemma n9 : normEDS b c d 9 = normEDS b c d 6 * (d * b) ^ 3 - c * normEDS b c d 5 ^ 3 := by
  have h := normEDS_odd b c d 4
  norm_num at h
  linear_combination h

lemma rel7 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 7)) * normEDS b c d (m + (j - 7))
      - (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2)
        * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := N7.main R b c d (m + j)
  rw [show m + j + 7 = m + (j + 7) by ring, show m + j - 7 = m + (j - 7) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n8 b c d hb, n7 b c d, n6 b c d hb, n5 b c d] at h
  linear_combination h

lemma gen (hb : b ≠ 0) (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (m : ℤ) :
    normEDS b c d (m + 8) * normEDS b c d (m - 8)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 8 ^ 2
      + normEDS b c d 9 * normEDS b c d 7 * normEDS b c d m ^ 2 = 0 := by
  have hpoly : normEDS b c d (m + 8) * normEDS b c d (m - 8)
      - (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2
        * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3)
        * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * normEDS b c d m ^ 2 = 0 := by
    by_cases hm : m = 3 ∨ m = 4
    · have h := cert_b b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j)
        (fun j => rel6 b c d hb m j) (fun j => rel7 b c d hb m j)
      rw [add_zero, show m + -8 = m - 8 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m + 1) * normEDS b c d (m + 2) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
    · have h := cert_a b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j)
        (fun j => rel6 b c d hb m j) (fun j => rel7 b c d hb m j)
      rw [add_zero, show m + -4 = m - 4 by ring, show m + -3 = m - 3 by ring,
        show m + -8 = m - 8 by ring, show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m - 4) * normEDS b c d (m - 3) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      exact (mul_eq_zero.mp h).resolve_left hne
  rw [n9 b c d, n8 b c d hb, n7 b c d, n6 b c d hb, n5 b c d]
  linear_combination hpoly

end Gen

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 8) * normEDS b c d (m - 8)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 8 ^ 2
      + normEDS b c d 9 * normEDS b c d 7 * normEDS b c d m ^ 2 = 0 := by
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

end MPP.Solutions.Bsd335
