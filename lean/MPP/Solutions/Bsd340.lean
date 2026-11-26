import Mathlib

namespace MPP.Solutions.Bsd340

theorem main : ∀ (a p : ℤ), 1 < p → (∀ m n : ℤ, ¬ p ∣ m → 0 ≤ m ^ 2 - a * m * n + p * n ^ 2) → a ^ 2 ≤ 4 * p := by
  intro a p hp h
  by_cases hd : p ∣ a
  · obtain ⟨k, rfl⟩ := hd
    have hn : ¬ p ∣ (p * k + 1) := by
      intro h1
      have h2 : p ∣ 1 := by
        have := dvd_sub h1 (dvd_mul_right p k)
        simpa using this
      have := Int.le_of_dvd (by norm_num) h2
      omega
    have h2 := h (p * k + 1) 2 hn
    have h4 : p * k ^ 2 ≤ 4 := by
      by_contra hc
      have h5 : 4 + 1 ≤ p * k ^ 2 := Int.lt_iff_add_one_le.mp (not_le.mp hc)
      nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℤ) ≤ p by omega)]
    nlinarith [mul_le_mul_of_nonneg_left h4 (show (0 : ℤ) ≤ p by omega)]
  · have h1 := h a 2 hd
    nlinarith [h1]

end MPP.Solutions.Bsd340
