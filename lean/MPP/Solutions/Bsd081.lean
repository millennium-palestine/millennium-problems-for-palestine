import Mathlib

namespace MPP.Solutions.Bsd081

theorem main : ∀ (p q x u v w xR yR : ℚ),
    u ^ 2 - 2 * q * v * w = x →
    2 * u * v - 2 * p * v * w - q * w ^ 2 = -1 →
    v ^ 2 + 2 * u * w - p * w ^ 2 = 0 →
    xR = x + ((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2 →
    yR = (3 * u - 2 * p * w) * (((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2) -
      (p ^ 2 * u * w ^ 2 - p * q * v * w ^ 2 - 2 * p * u ^ 2 * w + p * u * v ^ 2 +
        q ^ 2 * w ^ 3 + 3 * q * u * v * w - q * v ^ 3 + u ^ 3) →
    yR ^ 2 = xR ^ 3 + p * xR + q ∧ (3 * xR ^ 2 + p) ^ 2 = 4 * yR ^ 2 * (x + 2 * xR) := by
  intro p q x u v w xR yR hx hE1 hE2 hxR hyR
  -- w ≠ 0: otherwise v = 0 and then 0 = -1
  have hw : w ≠ 0 := by
    intro hw0
    subst hw0
    have hv2 : v ^ 2 = 0 := by linear_combination hE2
    have hv : v = 0 := pow_eq_zero_iff two_ne_zero |>.mp hv2
    subst hv
    norm_num at hE1
  -- solve the two linear equations for u and q
  have hu : u = (p * w ^ 2 - v ^ 2) / (2 * w) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hw)]
    linear_combination hE2
  have hq : q = (1 + 2 * u * v - 2 * p * v * w) / w ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hw)]
    linear_combination (-1 : ℚ) * hE1
  subst hu
  subst hq
  subst hx
  subst hxR
  subst hyR
  constructor
  · field_simp
    ring
  · field_simp
    ring

end MPP.Solutions.Bsd081
