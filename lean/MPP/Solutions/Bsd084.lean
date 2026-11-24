import Mathlib

namespace MPP.Solutions.Bsd084

theorem main : ∀ (p q e x a u v xR yR : ℚ),
    e ^ 3 + p * e + q = 0 →
    a ^ 2 = x - e →
    u ^ 2 - v ^ 2 * (e ^ 2 + p) = x →
    2 * u * v - e * v ^ 2 = -1 →
    xR = x + (a * (2 * u - e * v) + (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p))) →
    yR = (a + (2 * u - e * v)) * (a * (2 * u - e * v) + (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p))) -
      a * (u ^ 2 - e * u * v + v ^ 2 * (e ^ 2 + p)) →
    yR ^ 2 = xR ^ 3 + p * xR + q ∧ (3 * xR ^ 2 + p) ^ 2 = 4 * yR ^ 2 * (x + 2 * xR) := by
  intro p q e x a u v xR yR hq ha hu hv hxR hyR
  have hv0 : v ≠ 0 := by
    intro h0
    subst h0
    norm_num at hv
  have hq' : q = -e ^ 3 - p * e := by linear_combination hq
  have hx' : x = a ^ 2 + e := by linear_combination -ha
  have hp' : p = (u ^ 2 - x - e ^ 2 * v ^ 2) / v ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hv0)]
    linear_combination -hu
  have hu' : u = (e * v ^ 2 - 1) / (2 * v) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hv0)]
    linear_combination hv
  subst hx'
  subst hu'
  subst hp'
  subst hq'
  subst hxR
  subst hyR
  constructor
  · field_simp
    ring
  · field_simp
    ring

end MPP.Solutions.Bsd084
