import Mathlib

namespace MPP.Solutions.Bsd015

open LSeries

theorem main : ∀ (a : ℕ → ℂ) (s : ℂ),
    (∀ n : ℕ, 0 < n → ‖a n‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) →
    3 / 2 < s.re → LSeriesSummable a s := by
  intro a s ha hs
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = s.re - 1 / 2 := ⟨_, rfl⟩
  have hu : 1 < u := by rw [hu_def]; linarith
  -- the divisor-count sequence is summable at the real point u > 1
  have hD : LSeriesSummable (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) (u : ℂ) := by
    have h1 : LSeriesSummable (1 : ℕ → ℂ) (u : ℂ) :=
      LSeriesSummable_one_iff.mpr (by simpa using hu)
    have h2 := h1.convolution h1
    refine (LSeriesSummable_congr (u : ℂ) (fun {n} hn => ?_)).mp h2
    have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]
    rw [LSeries.convolution_def]
    simp [hc]
  -- termwise comparison with the divisor series
  have hbound : ∀ n : ℕ, ‖term a s n‖ ≤
      ‖term (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) (u : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ u * Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnR]
        congr 1
        rw [hu_def]
        ring
      have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
      have hpu : 0 < (n : ℝ) ^ u := Real.rpow_pos_of_pos hnR u
      rw [norm_term_eq, norm_term_eq, if_neg (by omega), if_neg (by omega), Complex.ofReal_re,
        hsplit]
      simp only [Complex.norm_natCast]
      calc ‖a n‖ / ((n : ℝ) ^ u * Real.sqrt (n : ℝ))
          ≤ ((n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) / ((n : ℝ) ^ u * Real.sqrt (n : ℝ)) :=
            div_le_div_of_nonneg_right (ha n hn) (by positivity)
        _ = (n.divisors.card : ℝ) / (n : ℝ) ^ u := by
            field_simp
  have hsum : Summable (fun n => ‖term (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) (u : ℂ) n‖) :=
    hD.norm
  exact Summable.of_norm_bounded hsum hbound

end MPP.Solutions.Bsd015
