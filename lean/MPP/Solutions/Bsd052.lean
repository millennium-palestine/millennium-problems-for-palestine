import Mathlib

namespace MPP.Solutions.Bsd052

theorem main : ∀ (p q : ℚ) (R : Type) [CommRing R] [Algebra ℚ R] (t : R),
    t ^ 3 + algebraMap ℚ R p * t + algebraMap ℚ R q = 0 →
    ∀ (x1 y1 x2 y2 lam x3 : ℚ), y1 ^ 2 = x1 ^ 3 + p * x1 + q → y2 ^ 2 = x2 ^ 3 + p * x2 + q →
      x1 ≠ x2 → lam * (x1 - x2) = y1 - y2 → x3 = lam ^ 2 - x1 - x2 →
      (algebraMap ℚ R x1 - t) * (algebraMap ℚ R x2 - t) * (algebraMap ℚ R x3 - t) =
        (algebraMap ℚ R y1 - algebraMap ℚ R lam * (algebraMap ℚ R x1 - t)) ^ 2 := by
  intro p q R _ _ t ht x1 y1 x2 y2 lam x3 h1 h2 hne hY hX
  have hL : lam * (y1 + y2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + p := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
    linear_combination (y1 + y2) * hY + h1 - h2
  have hL' := congrArg (algebraMap ℚ R) hL
  have hY' := congrArg (algebraMap ℚ R) hY
  have h1' := congrArg (algebraMap ℚ R) h1
  have hX' := congrArg (algebraMap ℚ R) hX
  simp only [map_mul, map_add, map_sub, map_pow] at hL' hY' h1' hX'
  linear_combination (-1 : R) * h1' + (algebraMap ℚ R x1 - t) * hL'
    - (algebraMap ℚ R x1 - t) * algebraMap ℚ R lam * hY' - ht
    + (algebraMap ℚ R x1 - t) * (algebraMap ℚ R x2 - t) * hX'

end MPP.Solutions.Bsd052
