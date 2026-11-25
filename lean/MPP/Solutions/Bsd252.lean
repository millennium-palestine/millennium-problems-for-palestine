import Mathlib

namespace MPP.Solutions.Bsd252

theorem main : ∀ (a p : ℝ) (z : ℂ), z + starRingEnd ℂ z = (a : ℂ) → z * starRingEnd ℂ z = (p : ℂ) →
    ∀ m n : ℝ, 0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  intro a p z hsum hprod m n
  have key : ((m : ℂ) - (n : ℂ) * z) * starRingEnd ℂ ((m : ℂ) - (n : ℂ) * z) =
      ((m ^ 2 - a * m * n + p * n ^ 2 : ℝ) : ℂ) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (-(m : ℂ) * (n : ℂ)) * hsum + (n : ℂ) ^ 2 * hprod
  rw [Complex.mul_conj] at key
  have h2 : Complex.normSq ((m : ℂ) - (n : ℂ) * z) = m ^ 2 - a * m * n + p * n ^ 2 :=
    Complex.ofReal_injective key
  rw [← h2]
  exact Complex.normSq_nonneg _

end MPP.Solutions.Bsd252
