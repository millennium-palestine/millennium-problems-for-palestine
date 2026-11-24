import Mathlib

namespace MPP.Solutions.Bsd076

theorem main : ∀ (p q : ℚ) (K : Type) [Field K] [Algebra ℚ K] (t : K),
    t ^ 3 + algebraMap ℚ K p * t + algebraMap ℚ K q = 0 →
    ∀ (x y lam x3 : ℚ), y ^ 2 = x ^ 3 + p * x + q → algebraMap ℚ K x ≠ t →
      lam * (2 * y) = 3 * x ^ 2 + p → x3 = lam ^ 2 - 2 * x →
      ∃ r : K, algebraMap ℚ K x3 - t = r ^ 2 := by
  intro p q K _ _ t ht x y lam x3 hy hne hl hx3
  have hcurve := congrArg (algebraMap ℚ K) hy
  have hslope := congrArg (algebraMap ℚ K) hl
  have hx3K := congrArg (algebraMap ℚ K) hx3
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at hcurve hslope hx3K
  have hxt : algebraMap ℚ K x - t ≠ 0 := sub_ne_zero.mpr hne
  have hid : (algebraMap ℚ K x - t) ^ 2 * (algebraMap ℚ K x3 - t) =
      (algebraMap ℚ K y - algebraMap ℚ K lam * (algebraMap ℚ K x - t)) ^ 2 := by
    rw [hx3K]
    linear_combination (-1 : K) * hcurve + (algebraMap ℚ K x - t) * hslope - ht
  refine ⟨(algebraMap ℚ K y - algebraMap ℚ K lam * (algebraMap ℚ K x - t)) / (algebraMap ℚ K x - t), ?_⟩
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hxt)]
  linear_combination hid

end MPP.Solutions.Bsd076
