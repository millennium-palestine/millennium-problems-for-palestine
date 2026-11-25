import Mathlib

namespace MPP.Solutions.Bsd261

theorem main : ∀ (p : ℕ) [Fact p.Prime] (ρ : MulChar (ZMod p) ℂ),
    (∀ x : ZMod p, ρ x ^ 2 = ((quadraticChar (ZMod p) x : ℤ) : ℂ)) →
    ∀ t : ZMod p, starRingEnd ℂ (ρ t) = ρ t ^ 3 := by
  intro p _ ρ hρ t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [MulChar.map_nonunit ρ not_isUnit_zero]
    simp
  · have h2 : ((quadraticChar (ZMod p) t : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast quadraticChar_sq_one ht
    have h4 : ρ t ^ 4 = 1 := by
      have : ρ t ^ 4 = ((quadraticChar (ZMod p) t : ℤ) : ℂ) ^ 2 := by
        rw [← hρ t]
        ring
      rw [this, h2]
    have hn : Complex.normSq (ρ t) = 1 := by
      have h := congrArg Complex.normSq h4
      rw [map_pow, map_one] at h
      exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) (by norm_num)).mp h
    have hz : ρ t ≠ 0 := by
      intro h
      rw [h] at h4
      norm_num at h4
    have hmul : ρ t * starRingEnd ℂ (ρ t) = 1 := by
      rw [Complex.mul_conj, hn]
      norm_num
    have hc : ρ t * (starRingEnd ℂ (ρ t) - ρ t ^ 3) = 0 := by
      linear_combination hmul - h4
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h hz
    · exact sub_eq_zero.mp h

end MPP.Solutions.Bsd261
