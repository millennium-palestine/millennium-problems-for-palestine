import Mathlib

namespace MPP.Solutions.Bsd063

theorem main : ∀ (p q e : ℚ), e ^ 3 + p * e + q = 0 →
    ∀ (x y lam x3 : ℚ), y ^ 2 = x ^ 3 + p * x + q → x ≠ e → lam * (2 * y) = 3 * x ^ 2 + p →
      x3 = lam ^ 2 - 2 * x → ∃ r : ℚ, x3 - e = r ^ 2 := by
  intro p q e he x y lam x3 hy hne hl hx3
  have hxe : x - e ≠ 0 := sub_ne_zero.mpr hne
  have hid : (x - e) ^ 2 * (x3 - e) = (y - lam * (x - e)) ^ 2 := by
    rw [hx3]
    linear_combination (-1 : ℚ) * hy + (x - e) * hl - he
  refine ⟨(y - lam * (x - e)) / (x - e), ?_⟩
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hxe)]
  linear_combination hid

end MPP.Solutions.Bsd063
