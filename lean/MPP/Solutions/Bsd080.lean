import Mathlib

namespace MPP.Solutions.Bsd080

theorem main : ∀ (p q : ℚ) (K : Type) [Field K] [Algebra ℚ K] (t : K),
    t ^ 3 + algebraMap ℚ K p * t + algebraMap ℚ K q = 0 →
    ∀ (x y : ℚ), y ^ 2 = x ^ 3 + p * x + q → algebraMap ℚ K x = t → y = 0 := by
  intro p q K _ _ t ht x y hy hx
  have hK := congrArg (algebraMap ℚ K) hy
  simp only [map_add, map_mul, map_pow] at hK
  have hsq : (algebraMap ℚ K y) ^ 2 = 0 := by
    rw [hK, hx]
    linear_combination ht
  have hy0 : algebraMap ℚ K y = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  exact (algebraMap ℚ K).injective (by rw [hy0, map_zero])

end MPP.Solutions.Bsd080
