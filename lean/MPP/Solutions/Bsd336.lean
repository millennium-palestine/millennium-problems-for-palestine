import Mathlib
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd320
import MPP.Solutions.Bsd323
import MPP.Solutions.Bsd324
import MPP.Solutions.Bsd325
import MPP.Solutions.Bsd328
import MPP.Solutions.Bsd335

namespace MPP.Solutions.Bsd336

/-! The n = 9 elliptic-net relation `N(m+9) N(m-9) - N(m+1) N(m-1) N(9)^2 + N(10) N(8) N(m)^2 = 0`
for `normEDS`, in an arbitrary commutative ring.

Uses the relations of n = 2..8 (bsd-323, bsd-324, bsd-325, bsd-320, bsd-328, bsd-335) at shifted indices.
Two certificates express the bracket times `N(m-6) N(m-1)` (resp. `N(m-8) N(m+1)`) as a combination of those
relations, an exact identity in `Z[b, c, d]` with integer coefficients (each certificate is scaled by a
positive integer, found by an L1 search and exact rational solve). The bracket is then zero in the universal
domain `MvPolynomial (Fin 3) ℤ`, where normEDS is nonzero off zero (bsd-225), and the identity is transferred
to `A` by evaluation at `![b, c, d]`. -/

/-! Certificate for the multiplier X(-6) X(-1): the n = 9 bracket times N(m-6)N(m-1) is a combination of the n = 2..8 relations. -/
lemma cert_a {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - (b ^ 2) * X (j + 1) * X (j - 1) + (c) * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - (c ^ 2) * X (j + 1) * X (j - 1) + (d * b * b) * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - ((d * b) ^ 2) * X (j + 1) * X (j - 1) + ((d * b ^ 4 - c ^ 3) * c) * X j ^ 2 = 0)
    (h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - ((d * b ^ 4 - c ^ 3) ^ 2) * X (j + 1) * X (j - 1) + (b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X j ^ 2 = 0)
    (h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - ((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2) * X (j + 1) * X (j - 1) + ((c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3)) * X j ^ 2 = 0)
    (h7 : ∀ j : ℤ, X (j + 7) * X (j - 7) - ((c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2) * X (j + 1) * X (j - 1) + ((c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2))) * X j ^ 2 = 0)
    (h8 : ∀ j : ℤ, X (j + 8) * X (j - 8) - ((c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2) * X (j + 1) * X (j - 1) + (((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3)) * X j ^ 2 = 0)
    : 192074 * (X (-6) * X (-1) * (X 9 * X (-9) - (((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) ^ 2) * X 1 * X (-1) + ((b * (d * b ^ 4 - c ^ 3) * (d ^ 2 * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) - c ^ 3 * ((d * b ^ 4 - c ^ 3) - d ^ 2) ^ 2)) * (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2)) * X 0 ^ 2)) = 0 := by
  have e2_m3 := h2 (-3)
  have e2_m1 := h2 (-1)
  have e2_1 := h2 (1)
  have e2_3 := h2 (3)
  have e3_m2 := h3 (-2)
  have e3_0 := h3 (0)
  have e3_2 := h3 (2)
  have e3_4 := h3 (4)
  have e4_m3 := h4 (-3)
  have e4_m1 := h4 (-1)
  have e4_1 := h4 (1)
  have e4_3 := h4 (3)
  have e5_m2 := h5 (-2)
  have e5_0 := h5 (0)
  have e5_2 := h5 (2)
  have e5_4 := h5 (4)
  have e6_m3 := h6 (-3)
  have e6_m1 := h6 (-1)
  have e6_1 := h6 (1)
  have e7_m2 := h7 (-2)
  have e7_0 := h7 (0)
  have e8_m1 := h8 (-1)
  norm_num at e2_m3 e2_m1 e2_1 e2_3 e3_m2 e3_0 e3_2 e3_4 e4_m3 e4_m1 e4_1 e4_3 e5_m2 e5_0 e5_2 e5_4 e6_m3 e6_m1 e6_1 e7_m2 e7_0 e8_m1
  linear_combination
    (52997) * (c ^ 2 * d ^ 8) * X (-6) * X (5) * e2_m3
    + (-33723) * (c ^ 5 * d ^ 6) * X (-6) * X (5) * e2_m3
    + (-940976) * (c ^ 11 * d ^ 2) * X (-6) * X (5) * e2_m3
    + (-365459) * (c ^ 14) * X (-6) * X (5) * e2_m3
    + (53962) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-6) * X (5) * e2_m3
    + (-341097) * (b ^ 4 * c ^ 5 * d ^ 5) * X (-6) * X (5) * e2_m3
    + (2233484) * (b ^ 4 * c ^ 8 * d ^ 3) * X (-6) * X (5) * e2_m3
    + (1222514) * (b ^ 4 * c ^ 11 * d ^ 1) * X (-6) * X (5) * e2_m3
    + (388323) * (b ^ 8 * c ^ 2 * d ^ 6) * X (-6) * X (5) * e2_m3
    + (-1469618) * (b ^ 8 * c ^ 5 * d ^ 4) * X (-6) * X (5) * e2_m3
    + (-1387577) * (b ^ 8 * c ^ 8 * d ^ 2) * X (-6) * X (5) * e2_m3
    + (177110) * (b ^ 12 * c ^ 2 * d ^ 5) * X (-6) * X (5) * e2_m3
    + (569448) * (b ^ 12 * c ^ 5 * d ^ 3) * X (-6) * X (5) * e2_m3
    + (-38926) * (b ^ 16 * c ^ 2 * d ^ 4) * X (-6) * X (5) * e2_m3
    + (-35653) * (c ^ 4 * d ^ 10) * X (-6) * X (1) * e2_m1
    + (15414) * (c ^ 7 * d ^ 8) * X (-6) * X (1) * e2_m1
    + (16379) * (c ^ 10 * d ^ 6) * X (-6) * X (1) * e2_m1
    + (-19004) * (c ^ 13 * d ^ 4) * X (-6) * X (1) * e2_m1
    + (-1660) * (c ^ 16 * d ^ 2) * X (-6) * X (1) * e2_m1
    + (50372) * (b ^ 4 * c ^ 10 * d ^ 5) * X (-6) * X (1) * e2_m1
    + (-35653) * (b ^ 8 * c ^ 1 * d ^ 10) * X (-6) * X (1) * e2_m1
    + (-17344) * (b ^ 8 * c ^ 4 * d ^ 8) * X (-6) * X (1) * e2_m1
    + (1660) * (b ^ 8 * c ^ 10 * d ^ 4) * X (-6) * X (1) * e2_m1
    + (-46261) * (b ^ 12 * c ^ 1 * d ^ 9) * X (-6) * X (1) * e2_m1
    + (-169552) * (b ^ 12 * c ^ 4 * d ^ 7) * X (-6) * X (1) * e2_m1
    + (-35606) * (b ^ 12 * c ^ 7 * d ^ 5) * X (-6) * X (1) * e2_m1
    + (138184) * (b ^ 16 * c ^ 1 * d ^ 8) * X (-6) * X (1) * e2_m1
    + (74532) * (b ^ 16 * c ^ 4 * d ^ 6) * X (-6) * X (1) * e2_m1
    + (-38926) * (b ^ 20 * c ^ 1 * d ^ 7) * X (-6) * X (1) * e2_m1
    + (35653) * (c ^ 3 * d ^ 10) * X (-6) * X (-3) * e2_1
    + (-68411) * (c ^ 6 * d ^ 8) * X (-6) * X (-3) * e2_1
    + (1660) * (c ^ 12 * d ^ 4) * X (-6) * X (-3) * e2_1
    + (35653) * (b ^ 4 * c ^ 3 * d ^ 9) * X (-6) * X (-3) * e2_1
    + (1660) * (b ^ 4 * c ^ 9 * d ^ 5) * X (-6) * X (-3) * e2_1
    + (52997) * (b ^ 8 * d ^ 10) * X (-6) * X (-3) * e2_1
    + (-52032) * (b ^ 8 * c ^ 3 * d ^ 8) * X (-6) * X (-3) * e2_1
    + (99258) * (b ^ 12 * d ^ 9) * X (-6) * X (-3) * e2_1
    + (35606) * (b ^ 12 * c ^ 3 * d ^ 7) * X (-6) * X (-3) * e2_1
    + (-38926) * (b ^ 16 * d ^ 8) * X (-6) * X (-3) * e2_1
    + (20099) * (c ^ 5 * d ^ 4) * X (-7) * X (-6) * e2_3
    + (-20099) * (c ^ 8 * d ^ 2) * X (-7) * X (-6) * e2_3
    + (20099) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-7) * X (-6) * e2_3
    + (-141101) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-7) * X (-6) * e2_3
    + (-52997) * (c ^ 4 * d ^ 8) * X (-6) * X (3) * e3_m2
    + (-161106) * (c ^ 7 * d ^ 6) * X (-6) * X (3) * e3_m2
    + (-90830) * (c ^ 10 * d ^ 4) * X (-6) * X (3) * e3_m2
    + (-17279) * (c ^ 16) * X (-6) * X (3) * e3_m2
    + (112730) * (b ^ 4 * c ^ 4 * d ^ 7) * X (-6) * X (3) * e3_m2
    + (202400) * (b ^ 4 * c ^ 13 * d ^ 1) * X (-6) * X (3) * e3_m2
    + (-52997) * (b ^ 8 * c ^ 1 * d ^ 8) * X (-6) * X (3) * e3_m2
    + (190981) * (b ^ 8 * c ^ 4 * d ^ 6) * X (-6) * X (3) * e3_m2
    + (53890) * (b ^ 8 * c ^ 7 * d ^ 4) * X (-6) * X (3) * e3_m2
    + (-602784) * (b ^ 8 * c ^ 10 * d ^ 2) * X (-6) * X (3) * e3_m2
    + (-46261) * (b ^ 12 * c ^ 1 * d ^ 7) * X (-6) * X (3) * e3_m2
    + (820632) * (b ^ 12 * c ^ 7 * d ^ 3) * X (-6) * X (3) * e3_m2
    + (-53890) * (b ^ 16 * c ^ 1 * d ^ 6) * X (-6) * X (3) * e3_m2
    + (-556117) * (b ^ 16 * c ^ 4 * d ^ 4) * X (-6) * X (3) * e3_m2
    + (153148) * (b ^ 20 * c ^ 1 * d ^ 5) * X (-6) * X (3) * e3_m2
    + (-35653) * (c ^ 3 * d ^ 10) * X (-6) * X (-1) * e3_0
    + (15414) * (c ^ 6 * d ^ 8) * X (-6) * X (-1) * e3_0
    + (-161106) * (c ^ 9 * d ^ 6) * X (-6) * X (-1) * e3_0
    + (-59592) * (c ^ 12 * d ^ 4) * X (-6) * X (-1) * e3_0
    + (-17984) * (c ^ 15 * d ^ 2) * X (-6) * X (-1) * e3_0
    + (21509) * (c ^ 18) * X (-6) * X (-1) * e3_0
    + (-35653) * (b ^ 4 * c ^ 3 * d ^ 9) * X (-6) * X (-1) * e3_0
    + (218724) * (b ^ 4 * c ^ 6 * d ^ 7) * X (-6) * X (-1) * e3_0
    + (-103424) * (b ^ 4 * c ^ 9 * d ^ 5) * X (-6) * X (-1) * e3_0
    + (172604) * (b ^ 4 * c ^ 12 * d ^ 3) * X (-6) * X (-1) * e3_0
    + (-124943) * (b ^ 8 * c ^ 3 * d ^ 8) * X (-6) * X (-1) * e3_0
    + (477052) * (b ^ 8 * c ^ 6 * d ^ 6) * X (-6) * X (-1) * e3_0
    + (-228139) * (b ^ 8 * c ^ 9 * d ^ 4) * X (-6) * X (-1) * e3_0
    + (-365009) * (b ^ 12 * c ^ 3 * d ^ 7) * X (-6) * X (-1) * e3_0
    + (292604) * (b ^ 12 * c ^ 6 * d ^ 5) * X (-6) * X (-1) * e3_0
    + (-73989) * (b ^ 12 * c ^ 9 * d ^ 3) * X (-6) * X (-1) * e3_0
    + (192074) * (b ^ 16 * d ^ 8) * X (-6) * X (-1) * e3_0
    + (-219085) * (b ^ 16 * c ^ 3 * d ^ 6) * X (-6) * X (-1) * e3_0
    + (40433) * (b ^ 16 * c ^ 6 * d ^ 4) * X (-6) * X (-1) * e3_0
    + (12047) * (b ^ 20 * c ^ 3 * d ^ 5) * X (-6) * X (-1) * e3_0
    + (-17344) * (c ^ 2 * d ^ 8) * X (-6) * X (-5) * e3_2
    + (-17344) * (c ^ 5 * d ^ 6) * X (-6) * X (-5) * e3_2
    + (17344) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-6) * X (-5) * e3_2
    + (192074) * (c ^ 1 * d ^ 2) * X (-9) * X (-6) * e3_4
    + (192074) * (c ^ 4) * X (-9) * X (-6) * e3_4
    + (-192074) * (b ^ 4 * c ^ 1 * d ^ 1) * X (-9) * X (-6) * e3_4
    + (-70341) * (c ^ 5 * d ^ 4) * X (-6) * X (5) * e4_m3
    + (-732578) * (c ^ 8 * d ^ 2) * X (-6) * X (5) * e4_m3
    + (-60698) * (b ^ 4 * c ^ 2 * d ^ 5) * X (-6) * X (5) * e4_m3
    + (1345331) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-6) * X (5) * e4_m3
    + (-572768) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-6) * X (5) * e4_m3
    + (35653) * (c ^ 4 * d ^ 8) * X (-6) * X (1) * e4_m1
    + (126418) * (c ^ 7 * d ^ 6) * X (-6) * X (1) * e4_m1
    + (90830) * (c ^ 10 * d ^ 4) * X (-6) * X (1) * e4_m1
    + (17279) * (c ^ 16) * X (-6) * X (1) * e4_m1
    + (-60698) * (b ^ 4 * c ^ 4 * d ^ 7) * X (-6) * X (1) * e4_m1
    + (-202400) * (b ^ 4 * c ^ 13 * d ^ 1) * X (-6) * X (1) * e4_m1
    + (35653) * (b ^ 8 * c ^ 1 * d ^ 8) * X (-6) * X (1) * e4_m1
    + (-190981) * (b ^ 8 * c ^ 4 * d ^ 6) * X (-6) * X (1) * e4_m1
    + (-53890) * (b ^ 8 * c ^ 7 * d ^ 4) * X (-6) * X (1) * e4_m1
    + (602784) * (b ^ 8 * c ^ 10 * d ^ 2) * X (-6) * X (1) * e4_m1
    + (46261) * (b ^ 12 * c ^ 1 * d ^ 7) * X (-6) * X (1) * e4_m1
    + (-820632) * (b ^ 12 * c ^ 7 * d ^ 3) * X (-6) * X (1) * e4_m1
    + (53890) * (b ^ 16 * c ^ 1 * d ^ 6) * X (-6) * X (1) * e4_m1
    + (556117) * (b ^ 16 * c ^ 4 * d ^ 4) * X (-6) * X (1) * e4_m1
    + (-153148) * (b ^ 20 * c ^ 1 * d ^ 5) * X (-6) * X (1) * e4_m1
    + (-52997) * (c ^ 3 * d ^ 8) * X (-6) * X (-3) * e4_1
    + (33723) * (c ^ 6 * d ^ 6) * X (-6) * X (-3) * e4_1
    + (-17344) * (c ^ 9 * d ^ 4) * X (-6) * X (-3) * e4_1
    + (-1660) * (c ^ 12 * d ^ 2) * X (-6) * X (-3) * e4_1
    + (-965) * (b ^ 4 * c ^ 3 * d ^ 7) * X (-6) * X (-3) * e4_1
    + (34688) * (b ^ 4 * c ^ 6 * d ^ 5) * X (-6) * X (-3) * e4_1
    + (-1660) * (b ^ 4 * c ^ 9 * d ^ 3) * X (-6) * X (-3) * e4_1
    + (-52997) * (b ^ 8 * d ^ 8) * X (-6) * X (-3) * e4_1
    + (34688) * (b ^ 8 * c ^ 3 * d ^ 6) * X (-6) * X (-3) * e4_1
    + (-99258) * (b ^ 12 * d ^ 7) * X (-6) * X (-3) * e4_1
    + (-35606) * (b ^ 12 * c ^ 3 * d ^ 5) * X (-6) * X (-3) * e4_1
    + (38926) * (b ^ 16 * d ^ 6) * X (-6) * X (-3) * e4_1
    + (-20099) * (c ^ 5 * d ^ 2) * X (-7) * X (-6) * e4_3
    + (20099) * (c ^ 8) * X (-7) * X (-6) * e4_3
    + (-20099) * (b ^ 4 * c ^ 5 * d ^ 1) * X (-7) * X (-6) * e4_3
    + (141101) * (b ^ 8 * c ^ 2 * d ^ 2) * X (-7) * X (-6) * e4_3
    + (-20099) * (c ^ 6 * d ^ 4) * X (-6) * X (3) * e5_m2
    + (20099) * (c ^ 12) * X (-6) * X (3) * e5_m2
    + (-40198) * (b ^ 4 * c ^ 9 * d ^ 1) * X (-6) * X (3) * e5_m2
    + (141101) * (b ^ 8 * c ^ 3 * d ^ 4) * X (-6) * X (3) * e5_m2
    + (161200) * (b ^ 8 * c ^ 6 * d ^ 2) * X (-6) * X (3) * e5_m2
    + (-141101) * (b ^ 12 * c ^ 3 * d ^ 3) * X (-6) * X (3) * e5_m2
    + (-35653) * (c ^ 2 * d ^ 8) * X (-6) * X (-1) * e5_0
    + (51067) * (c ^ 5 * d ^ 6) * X (-6) * X (-1) * e5_0
    + (940976) * (c ^ 11 * d ^ 2) * X (-6) * X (-1) * e5_0
    + (365459) * (c ^ 14) * X (-6) * X (-1) * e5_0
    + (-71306) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-6) * X (-1) * e5_0
    + (341097) * (b ^ 4 * c ^ 5 * d ^ 5) * X (-6) * X (-1) * e5_0
    + (-2233484) * (b ^ 4 * c ^ 8 * d ^ 3) * X (-6) * X (-1) * e5_0
    + (-1222514) * (b ^ 4 * c ^ 11 * d ^ 1) * X (-6) * X (-1) * e5_0
    + (-388323) * (b ^ 8 * c ^ 2 * d ^ 6) * X (-6) * X (-1) * e5_0
    + (1469618) * (b ^ 8 * c ^ 5 * d ^ 4) * X (-6) * X (-1) * e5_0
    + (1387577) * (b ^ 8 * c ^ 8 * d ^ 2) * X (-6) * X (-1) * e5_0
    + (-177110) * (b ^ 12 * c ^ 2 * d ^ 5) * X (-6) * X (-1) * e5_0
    + (-569448) * (b ^ 12 * c ^ 5 * d ^ 3) * X (-6) * X (-1) * e5_0
    + (38926) * (b ^ 16 * c ^ 2 * d ^ 4) * X (-6) * X (-1) * e5_0
    + (-17344) * (c ^ 1 * d ^ 6) * X (-6) * X (-5) * e5_2
    + (192074) * (1) * X (-9) * X (-6) * e5_4
    + (-52997) * (d ^ 4) * X (-6) * X (5) * e6_m3
    + (210058) * (c ^ 3 * d ^ 2) * X (-6) * X (5) * e6_m3
    + (365459) * (c ^ 6) * X (-6) * X (5) * e6_m3
    + (-99258) * (b ^ 4 * d ^ 3) * X (-6) * X (5) * e6_m3
    + (-491596) * (b ^ 4 * c ^ 3 * d ^ 1) * X (-6) * X (5) * e6_m3
    + (38926) * (b ^ 8 * d ^ 2) * X (-6) * X (5) * e6_m3
    + (50242) * (c ^ 5 * d ^ 4) * X (-6) * X (1) * e6_m1
    + (752677) * (c ^ 8 * d ^ 2) * X (-6) * X (1) * e6_m1
    + (60698) * (b ^ 4 * c ^ 2 * d ^ 5) * X (-6) * X (1) * e6_m1
    + (-1365430) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-6) * X (1) * e6_m1
    + (713869) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-6) * X (1) * e6_m1
    + (17344) * (c ^ 1 * d ^ 6) * X (-6) * X (-3) * e6_1
    + (52997) * (d ^ 4) * X (-6) * X (3) * e7_m2
    + (-17984) * (c ^ 3 * d ^ 2) * X (-6) * X (3) * e7_m2
    + (18689) * (c ^ 6) * X (-6) * X (3) * e7_m2
    + (99258) * (b ^ 4 * d ^ 3) * X (-6) * X (3) * e7_m2
    + (-84626) * (b ^ 4 * c ^ 3 * d ^ 1) * X (-6) * X (3) * e7_m2
    + (153148) * (b ^ 8 * d ^ 2) * X (-6) * X (3) * e7_m2
    + (20099) * (c ^ 5 * d ^ 2) * X (-6) * X (-1) * e7_0
    + (-20099) * (c ^ 8) * X (-6) * X (-1) * e7_0
    + (20099) * (b ^ 4 * c ^ 5 * d ^ 1) * X (-6) * X (-1) * e7_0
    + (-141101) * (b ^ 8 * c ^ 2 * d ^ 2) * X (-6) * X (-1) * e7_0
    + (-192074) * (c ^ 1 * d ^ 2) * X (-6) * X (1) * e8_m1
    + (-192074) * (c ^ 4) * X (-6) * X (1) * e8_m1
    + (192074) * (b ^ 4 * c ^ 1 * d ^ 1) * X (-6) * X (1) * e8_m1

/-! Certificate for the multiplier X(-8) X(1), used at m = 1 and m = 6 where N(m-6)N(m-1) vanishes. -/
lemma cert_b {A : Type} [CommRing A] (b c d : A) (X : ℤ → A)
    (h2 : ∀ j : ℤ, X (j + 2) * X (j - 2) - (b ^ 2) * X (j + 1) * X (j - 1) + (c) * X j ^ 2 = 0)
    (h3 : ∀ j : ℤ, X (j + 3) * X (j - 3) - (c ^ 2) * X (j + 1) * X (j - 1) + (d * b * b) * X j ^ 2 = 0)
    (h4 : ∀ j : ℤ, X (j + 4) * X (j - 4) - ((d * b) ^ 2) * X (j + 1) * X (j - 1) + ((d * b ^ 4 - c ^ 3) * c) * X j ^ 2 = 0)
    (h5 : ∀ j : ℤ, X (j + 5) * X (j - 5) - ((d * b ^ 4 - c ^ 3) ^ 2) * X (j + 1) * X (j - 1) + (b * b * c * d * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * X j ^ 2 = 0)
    (h6 : ∀ j : ℤ, X (j + 6) * X (j - 6) - ((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) ^ 2) * X (j + 1) * X (j - 1) + ((c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * (d * b ^ 4 - c ^ 3)) * X j ^ 2 = 0)
    (h7 : ∀ j : ℤ, X (j + 7) * X (j - 7) - ((c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) ^ 2) * X (j + 1) * X (j - 1) + ((c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2))) * X j ^ 2 = 0)
    (h8 : ∀ j : ℤ, X (j + 8) * X (j - 8) - ((c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2) * X (j + 1) * X (j - 1) + (((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3)) * X j ^ 2 = 0)
    : 141944 * (X (-8) * X (1) * (X 9 * X (-9) - (((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) ^ 2) * X 1 * X (-1) + ((b * (d * b ^ 4 - c ^ 3) * (d ^ 2 * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) - c ^ 3 * ((d * b ^ 4 - c ^ 3) - d ^ 2) ^ 2)) * (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2)) * X 0 ^ 2)) = 0 := by
  have e2_m3 := h2 (-3)
  have e2_m1 := h2 (-1)
  have e2_1 := h2 (1)
  have e2_3 := h2 (3)
  have e3_m4 := h3 (-4)
  have e3_m2 := h3 (-2)
  have e3_0 := h3 (0)
  have e3_2 := h3 (2)
  have e4_m3 := h4 (-3)
  have e4_m1 := h4 (-1)
  have e4_1 := h4 (1)
  have e4_3 := h4 (3)
  have e5_m4 := h5 (-4)
  have e5_m2 := h5 (-2)
  have e5_0 := h5 (0)
  have e5_2 := h5 (2)
  have e6_m1 := h6 (-1)
  have e6_1 := h6 (1)
  have e6_3 := h6 (3)
  have e7_0 := h7 (0)
  have e7_2 := h7 (2)
  have e8_1 := h8 (1)
  norm_num at e2_m3 e2_m1 e2_1 e2_3 e3_m4 e3_m2 e3_0 e3_2 e4_m3 e4_m1 e4_1 e4_3 e5_m4 e5_m2 e5_0 e5_2 e6_m1 e6_1 e6_3 e7_0 e7_2 e8_1
  linear_combination
    (-4159) * (c ^ 5 * d ^ 4) * X (-8) * X (7) * e2_m3
    + (-19277) * (c ^ 8 * d ^ 2) * X (-8) * X (7) * e2_m3
    + (9059) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-8) * X (7) * e2_m3
    + (-108693) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-8) * X (7) * e2_m3
    + (33555) * (c ^ 3 * d ^ 10) * X (-8) * X (3) * e2_m1
    + (-46977) * (c ^ 6 * d ^ 8) * X (-8) * X (3) * e2_m1
    + (4843) * (c ^ 12 * d ^ 4) * X (-8) * X (3) * e2_m1
    + (33555) * (b ^ 4 * c ^ 3 * d ^ 9) * X (-8) * X (3) * e2_m1
    + (11208) * (b ^ 4 * c ^ 9 * d ^ 5) * X (-8) * X (3) * e2_m1
    + (35624) * (b ^ 8 * d ^ 10) * X (-8) * X (3) * e2_m1
    + (4843) * (b ^ 8 * c ^ 6 * d ^ 6) * X (-8) * X (3) * e2_m1
    + (62682) * (b ^ 12 * d ^ 9) * X (-8) * X (3) * e2_m1
    + (-20894) * (b ^ 16 * d ^ 8) * X (-8) * X (3) * e2_m1
    + (-33555) * (c ^ 4 * d ^ 10) * X (-8) * X (-1) * e2_1
    + (11554) * (c ^ 10 * d ^ 6) * X (-8) * X (-1) * e2_1
    + (-3736) * (c ^ 13 * d ^ 4) * X (-8) * X (-1) * e2_1
    + (-20894) * (b ^ 4 * c ^ 13 * d ^ 3) * X (-8) * X (-1) * e2_1
    + (-22202) * (b ^ 8 * c ^ 1 * d ^ 10) * X (-8) * X (-1) * e2_1
    + (-47178) * (b ^ 8 * c ^ 4 * d ^ 8) * X (-8) * X (-1) * e2_1
    + (-30580) * (b ^ 8 * c ^ 7 * d ^ 6) * X (-8) * X (-1) * e2_1
    + (20894) * (b ^ 8 * c ^ 10 * d ^ 4) * X (-8) * X (-1) * e2_1
    + (-27058) * (b ^ 12 * c ^ 1 * d ^ 9) * X (-8) * X (-1) * e2_1
    + (-49260) * (b ^ 12 * c ^ 4 * d ^ 7) * X (-8) * X (-1) * e2_1
    + (83576) * (b ^ 16 * c ^ 1 * d ^ 8) * X (-8) * X (-1) * e2_1
    + (20894) * (b ^ 16 * c ^ 4 * d ^ 6) * X (-8) * X (-1) * e2_1
    + (-20894) * (b ^ 20 * c ^ 1 * d ^ 7) * X (-8) * X (-1) * e2_1
    + (46977) * (c ^ 2 * d ^ 8) * X (-8) * X (-5) * e2_3
    + (-36329) * (c ^ 5 * d ^ 6) * X (-8) * X (-5) * e2_3
    + (-4843) * (c ^ 8 * d ^ 4) * X (-8) * X (-5) * e2_3
    + (-677966) * (c ^ 11 * d ^ 2) * X (-8) * X (-5) * e2_3
    + (-263093) * (c ^ 14) * X (-8) * X (-5) * e2_3
    + (53688) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-8) * X (-5) * e2_3
    + (-258237) * (b ^ 4 * c ^ 5 * d ^ 5) * X (-8) * X (-5) * e2_3
    + (1639856) * (b ^ 4 * c ^ 8 * d ^ 3) * X (-8) * X (-5) * e2_3
    + (899900) * (b ^ 4 * c ^ 11 * d ^ 1) * X (-8) * X (-5) * e2_3
    + (325762) * (b ^ 8 * c ^ 2 * d ^ 6) * X (-8) * X (-5) * e2_3
    + (-1066360) * (b ^ 8 * c ^ 5 * d ^ 4) * X (-8) * X (-5) * e2_3
    + (-1031415) * (b ^ 8 * c ^ 8 * d ^ 2) * X (-8) * X (-5) * e2_3
    + (104470) * (b ^ 12 * c ^ 2 * d ^ 5) * X (-8) * X (-5) * e2_3
    + (415502) * (b ^ 12 * c ^ 5 * d ^ 3) * X (-8) * X (-5) * e2_3
    + (-20894) * (b ^ 16 * c ^ 2 * d ^ 4) * X (-8) * X (-5) * e2_3
    + (141944) * (c ^ 1 * d ^ 2) * X (-8) * X (9) * e3_m4
    + (141944) * (c ^ 4) * X (-8) * X (9) * e3_m4
    + (-141944) * (b ^ 4 * c ^ 1 * d ^ 1) * X (-8) * X (9) * e3_m4
    + (-13422) * (c ^ 2 * d ^ 8) * X (-8) * X (5) * e3_m2
    + (-8579) * (c ^ 5 * d ^ 6) * X (-8) * X (5) * e3_m2
    + (4843) * (c ^ 8 * d ^ 4) * X (-8) * X (5) * e3_m2
    + (13422) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-8) * X (5) * e3_m2
    + (-4843) * (b ^ 4 * c ^ 5 * d ^ 5) * X (-8) * X (5) * e3_m2
    + (-33555) * (c ^ 3 * d ^ 10) * X (-8) * X (1) * e3_0
    + (11353) * (c ^ 6 * d ^ 8) * X (-8) * X (1) * e3_0
    + (-92877) * (c ^ 9 * d ^ 6) * X (-8) * X (1) * e3_0
    + (13600) * (c ^ 15 * d ^ 2) * X (-8) * X (1) * e3_0
    + (17759) * (c ^ 18) * X (-8) * X (1) * e3_0
    + (-33555) * (b ^ 4 * c ^ 3 * d ^ 9) * X (-8) * X (1) * e3_0
    + (151062) * (b ^ 4 * c ^ 6 * d ^ 7) * X (-8) * X (1) * e3_0
    + (-124975) * (b ^ 4 * c ^ 9 * d ^ 5) * X (-8) * X (1) * e3_0
    + (63854) * (b ^ 4 * c ^ 12 * d ^ 3) * X (-8) * X (1) * e3_0
    + (-116708) * (b ^ 8 * c ^ 3 * d ^ 8) * X (-8) * X (1) * e3_0
    + (306482) * (b ^ 8 * c ^ 6 * d ^ 6) * X (-8) * X (1) * e3_0
    + (-122461) * (b ^ 8 * c ^ 9 * d ^ 4) * X (-8) * X (1) * e3_0
    + (-204540) * (b ^ 12 * c ^ 3 * d ^ 7) * X (-8) * X (1) * e3_0
    + (236782) * (b ^ 12 * c ^ 6 * d ^ 5) * X (-8) * X (1) * e3_0
    + (-58679) * (b ^ 12 * c ^ 9 * d ^ 3) * X (-8) * X (1) * e3_0
    + (141944) * (b ^ 16 * d ^ 8) * X (-8) * X (1) * e3_0
    + (-191775) * (b ^ 16 * c ^ 3 * d ^ 6) * X (-8) * X (1) * e3_0
    + (28563) * (b ^ 16 * c ^ 6 * d ^ 4) * X (-8) * X (1) * e3_0
    + (12357) * (b ^ 20 * c ^ 3 * d ^ 5) * X (-8) * X (1) * e3_0
    + (-35624) * (c ^ 4 * d ^ 8) * X (-8) * X (-3) * e3_2
    + (-92877) * (c ^ 7 * d ^ 6) * X (-8) * X (-3) * e3_2
    + (-34940) * (c ^ 10 * d ^ 4) * X (-8) * X (-3) * e3_2
    + (-22313) * (c ^ 16) * X (-8) * X (-3) * e3_2
    + (79814) * (b ^ 4 * c ^ 4 * d ^ 7) * X (-8) * X (-3) * e3_2
    + (-14529) * (b ^ 4 * c ^ 7 * d ^ 5) * X (-8) * X (-3) * e3_2
    + (160598) * (b ^ 4 * c ^ 13 * d ^ 1) * X (-8) * X (-3) * e3_2
    + (-35624) * (b ^ 8 * c ^ 1 * d ^ 8) * X (-8) * X (-3) * e3_2
    + (105711) * (b ^ 8 * c ^ 4 * d ^ 6) * X (-8) * X (-3) * e3_2
    + (-439782) * (b ^ 8 * c ^ 10 * d ^ 2) * X (-8) * X (-3) * e3_2
    + (-27058) * (b ^ 12 * c ^ 1 * d ^ 7) * X (-8) * X (-3) * e3_2
    + (58368) * (b ^ 12 * c ^ 4 * d ^ 5) * X (-8) * X (-3) * e3_2
    + (608072) * (b ^ 12 * c ^ 7 * d ^ 3) * X (-8) * X (-3) * e3_2
    + (-58368) * (b ^ 16 * c ^ 1 * d ^ 6) * X (-8) * X (-3) * e3_2
    + (-427625) * (b ^ 16 * c ^ 4 * d ^ 4) * X (-8) * X (-3) * e3_2
    + (121050) * (b ^ 20 * c ^ 1 * d ^ 5) * X (-8) * X (-3) * e3_2
    + (4159) * (c ^ 5 * d ^ 2) * X (-8) * X (7) * e4_m3
    + (19277) * (c ^ 8) * X (-8) * X (7) * e4_m3
    + (-9059) * (b ^ 4 * c ^ 5 * d ^ 1) * X (-8) * X (7) * e4_m3
    + (108693) * (b ^ 8 * c ^ 2 * d ^ 2) * X (-8) * X (7) * e4_m3
    + (-46977) * (c ^ 3 * d ^ 8) * X (-8) * X (3) * e4_m1
    + (24976) * (c ^ 6 * d ^ 6) * X (-8) * X (3) * e4_m1
    + (-3736) * (c ^ 9 * d ^ 4) * X (-8) * X (3) * e4_m1
    + (-6711) * (b ^ 4 * c ^ 3 * d ^ 7) * X (-8) * X (3) * e4_m1
    + (17158) * (b ^ 4 * c ^ 6 * d ^ 5) * X (-8) * X (3) * e4_m1
    + (-20894) * (b ^ 4 * c ^ 9 * d ^ 3) * X (-8) * X (3) * e4_m1
    + (-35624) * (b ^ 8 * d ^ 8) * X (-8) * X (3) * e4_m1
    + (-13422) * (b ^ 8 * c ^ 3 * d ^ 6) * X (-8) * X (3) * e4_m1
    + (-62682) * (b ^ 12 * d ^ 7) * X (-8) * X (3) * e4_m1
    + (20894) * (b ^ 16 * d ^ 6) * X (-8) * X (3) * e4_m1
    + (22202) * (c ^ 4 * d ^ 8) * X (-8) * X (-1) * e4_1
    + (70876) * (c ^ 7 * d ^ 6) * X (-8) * X (-1) * e4_1
    + (44626) * (c ^ 10 * d ^ 4) * X (-8) * X (-1) * e4_1
    + (22313) * (c ^ 16) * X (-8) * X (-1) * e4_1
    + (-39548) * (b ^ 4 * c ^ 4 * d ^ 7) * X (-8) * X (-1) * e4_1
    + (-160598) * (b ^ 4 * c ^ 13 * d ^ 1) * X (-8) * X (-1) * e4_1
    + (22202) * (b ^ 8 * c ^ 1 * d ^ 8) * X (-8) * X (-1) * e4_1
    + (-100868) * (b ^ 8 * c ^ 4 * d ^ 6) * X (-8) * X (-1) * e4_1
    + (439782) * (b ^ 8 * c ^ 10 * d ^ 2) * X (-8) * X (-1) * e4_1
    + (27058) * (b ^ 12 * c ^ 1 * d ^ 7) * X (-8) * X (-1) * e4_1
    + (-58368) * (b ^ 12 * c ^ 4 * d ^ 5) * X (-8) * X (-1) * e4_1
    + (-608072) * (b ^ 12 * c ^ 7 * d ^ 3) * X (-8) * X (-1) * e4_1
    + (58368) * (b ^ 16 * c ^ 1 * d ^ 6) * X (-8) * X (-1) * e4_1
    + (427625) * (b ^ 16 * c ^ 4 * d ^ 4) * X (-8) * X (-1) * e4_1
    + (-121050) * (b ^ 20 * c ^ 1 * d ^ 5) * X (-8) * X (-1) * e4_1
    + (-11353) * (c ^ 2 * d ^ 6) * X (-8) * X (-5) * e4_3
    + (-44203) * (c ^ 5 * d ^ 4) * X (-8) * X (-5) * e4_3
    + (-526186) * (c ^ 8 * d ^ 2) * X (-8) * X (-5) * e4_3
    + (-62254) * (b ^ 4 * c ^ 2 * d ^ 5) * X (-8) * X (-5) * e4_3
    + (989627) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-8) * X (-5) * e4_3
    + (-436396) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-8) * X (-5) * e4_3
    + (141944) * (1) * X (-8) * X (9) * e5_m4
    + (-13422) * (c ^ 1 * d ^ 6) * X (-8) * X (5) * e5_m2
    + (4843) * (c ^ 4 * d ^ 4) * X (-8) * X (5) * e5_m2
    + (-33555) * (c ^ 2 * d ^ 8) * X (-8) * X (1) * e5_0
    + (44908) * (c ^ 5 * d ^ 6) * X (-8) * X (1) * e5_0
    + (677966) * (c ^ 11 * d ^ 2) * X (-8) * X (1) * e5_0
    + (263093) * (c ^ 14) * X (-8) * X (1) * e5_0
    + (-67110) * (b ^ 4 * c ^ 2 * d ^ 7) * X (-8) * X (1) * e5_0
    + (263080) * (b ^ 4 * c ^ 5 * d ^ 5) * X (-8) * X (1) * e5_0
    + (-1639856) * (b ^ 4 * c ^ 8 * d ^ 3) * X (-8) * X (1) * e5_0
    + (-899900) * (b ^ 4 * c ^ 11 * d ^ 1) * X (-8) * X (1) * e5_0
    + (-325762) * (b ^ 8 * c ^ 2 * d ^ 6) * X (-8) * X (1) * e5_0
    + (1066360) * (b ^ 8 * c ^ 5 * d ^ 4) * X (-8) * X (1) * e5_0
    + (1031415) * (b ^ 8 * c ^ 8 * d ^ 2) * X (-8) * X (1) * e5_0
    + (-104470) * (b ^ 12 * c ^ 2 * d ^ 5) * X (-8) * X (1) * e5_0
    + (-415502) * (b ^ 12 * c ^ 5 * d ^ 3) * X (-8) * X (1) * e5_0
    + (20894) * (b ^ 16 * c ^ 2 * d ^ 4) * X (-8) * X (1) * e5_0
    + (4159) * (c ^ 6 * d ^ 4) * X (-8) * X (-3) * e5_2
    + (23436) * (c ^ 9 * d ^ 2) * X (-8) * X (-3) * e5_2
    + (19277) * (c ^ 12) * X (-8) * X (-3) * e5_2
    + (-13218) * (b ^ 4 * c ^ 6 * d ^ 3) * X (-8) * X (-3) * e5_2
    + (-28336) * (b ^ 4 * c ^ 9 * d ^ 1) * X (-8) * X (-3) * e5_2
    + (108693) * (b ^ 8 * c ^ 3 * d ^ 4) * X (-8) * X (-3) * e5_2
    + (117752) * (b ^ 8 * c ^ 6 * d ^ 2) * X (-8) * X (-3) * e5_2
    + (-108693) * (b ^ 12 * c ^ 3 * d ^ 3) * X (-8) * X (-3) * e5_2
    + (13422) * (c ^ 1 * d ^ 6) * X (-8) * X (3) * e6_m1
    + (-4843) * (c ^ 4 * d ^ 4) * X (-8) * X (3) * e6_m1
    + (11353) * (c ^ 2 * d ^ 6) * X (-8) * X (-1) * e6_1
    + (48362) * (c ^ 5 * d ^ 4) * X (-8) * X (-1) * e6_1
    + (545463) * (c ^ 8 * d ^ 2) * X (-8) * X (-1) * e6_1
    + (62254) * (b ^ 4 * c ^ 2 * d ^ 5) * X (-8) * X (-1) * e6_1
    + (-998686) * (b ^ 4 * c ^ 5 * d ^ 3) * X (-8) * X (-1) * e6_1
    + (545089) * (b ^ 8 * c ^ 2 * d ^ 4) * X (-8) * X (-1) * e6_1
    + (-35624) * (d ^ 4) * X (-8) * X (-5) * e6_3
    + (151780) * (c ^ 3 * d ^ 2) * X (-8) * X (-5) * e6_3
    + (263093) * (c ^ 6) * X (-8) * X (-5) * e6_3
    + (-62682) * (b ^ 4 * d ^ 3) * X (-8) * X (-5) * e6_3
    + (-373714) * (b ^ 4 * c ^ 3 * d ^ 1) * X (-8) * X (-5) * e6_3
    + (20894) * (b ^ 8 * d ^ 2) * X (-8) * X (-5) * e6_3
    + (-4159) * (c ^ 5 * d ^ 2) * X (-8) * X (1) * e7_0
    + (-19277) * (c ^ 8) * X (-8) * X (1) * e7_0
    + (9059) * (b ^ 4 * c ^ 5 * d ^ 1) * X (-8) * X (1) * e7_0
    + (-108693) * (b ^ 8 * c ^ 2 * d ^ 2) * X (-8) * X (1) * e7_0
    + (35624) * (d ^ 4) * X (-8) * X (-3) * e7_2
    + (-9836) * (c ^ 3 * d ^ 2) * X (-8) * X (-3) * e7_2
    + (20795) * (c ^ 6) * X (-8) * X (-3) * e7_2
    + (62682) * (b ^ 4 * d ^ 3) * X (-8) * X (-3) * e7_2
    + (-52118) * (b ^ 4 * c ^ 3 * d ^ 1) * X (-8) * X (-3) * e7_2
    + (121050) * (b ^ 8 * d ^ 2) * X (-8) * X (-3) * e7_2
    + (-141944) * (c ^ 1 * d ^ 2) * X (-8) * X (-1) * e8_1
    + (-141944) * (c ^ 4) * X (-8) * X (-1) * e8_1
    + (141944) * (b ^ 4 * c ^ 1 * d ^ 1) * X (-8) * X (-1) * e8_1


section Gen

variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] (b c d : R)

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
  have h := MPP.Solutions.Bsd335.N7.main R b c d (m + j)
  rw [show m + j + 7 = m + (j + 7) by ring, show m + j - 7 = m + (j - 7) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n8 b c d hb, n7 b c d, n6 b c d hb, n5 b c d] at h
  linear_combination h

lemma n10 (hb : b ≠ 0) : normEDS b c d 10 = (b * (d * b ^ 4 - c ^ 3) * (d ^ 2 * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) - c ^ 3 * ((d * b ^ 4 - c ^ 3) - d ^ 2) ^ 2)) := by
  have h := normEDS_even b c d 5
  norm_num at h
  rw [n7 b c d, n6 b c d hb, n5 b c d] at h
  apply mul_right_cancel₀ hb
  linear_combination h

lemma rel8 (hb : b ≠ 0) (m j : ℤ) :
    normEDS b c d (m + (j + 8)) * normEDS b c d (m + (j - 8))
      - (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2) ^ 2 * normEDS b c d (m + (j + 1)) * normEDS b c d (m + (j - 1))
      + ((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3) * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) * normEDS b c d (m + j) ^ 2 = 0 := by
  have h := MPP.Solutions.Bsd335.main R b c d (m + j)
  rw [show m + j + 8 = m + (j + 8) by ring, show m + j - 8 = m + (j - 8) by ring,
    show m + j + 1 = m + (j + 1) by ring, show m + j - 1 = m + (j - 1) by ring,
    n8 b c d hb, n9 b c d, n7 b c d, n6 b c d hb, n5 b c d] at h
  linear_combination h

lemma gen (hb : b ≠ 0) (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (m : ℤ) :
    normEDS b c d (m + 9) * normEDS b c d (m - 9)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 9 ^ 2
      + normEDS b c d 10 * normEDS b c d 8 * normEDS b c d m ^ 2 = 0 := by
  have hB : normEDS b c d (m + 9) * normEDS b c d (m - 9)
      - (((b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) * (d * b) ^ 3 - c * (d * b ^ 4 - c ^ 3) ^ 3)) ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + ((b * (d * b ^ 4 - c ^ 3) * (d ^ 2 * (c ^ 3 * (d * b ^ 4 - c ^ 3) - b ^ 4 * d ^ 3) - c ^ 3 * ((d * b ^ 4 - c ^ 3) - d ^ 2) ^ 2)) * (c ^ 2 * d * (b * c * ((d * b ^ 4 - c ^ 3) - d ^ 2)) - d * b * (d * b ^ 4 - c ^ 3) ^ 2)) * normEDS b c d m ^ 2 = 0 := by
    by_cases hm : m = 1 ∨ m = 6
    · have h := cert_b b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j)
        (fun j => rel6 b c d hb m j) (fun j => rel7 b c d hb m j)
        (fun j => rel8 b c d hb m j)
      rw [add_zero, show m + -8 = m - 8 by ring, show m + -9 = m - 9 by ring,
        show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m - 8) * normEDS b c d (m + 1) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      have hB := (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))).resolve_left hne
      linear_combination hB
    · have h := cert_a b c d (fun k => normEDS b c d (m + k))
        (fun j => rel2 b c d m j) (fun j => rel3 b c d m j)
        (fun j => rel4 b c d m j) (fun j => rel5 b c d hb m j)
        (fun j => rel6 b c d hb m j) (fun j => rel7 b c d hb m j)
        (fun j => rel8 b c d hb m j)
      rw [add_zero, show m + -6 = m - 6 by ring, show m + -9 = m - 9 by ring,
        show m + -1 = m - 1 by ring] at h
      have hne : normEDS b c d (m - 6) * normEDS b c d (m - 1) ≠ 0 :=
        mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))
      have hB := (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))).resolve_left hne
      linear_combination hB
  rw [n10 b c d hb, n9 b c d, n8 b c d hb, n6 b c d hb, n5 b c d]
  linear_combination hB

end Gen

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 9) * normEDS b c d (m - 9)
      - normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d 9 ^ 2
      + normEDS b c d 10 * normEDS b c d 8 * normEDS b c d m ^ 2 = 0 := by
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

end MPP.Solutions.Bsd336
