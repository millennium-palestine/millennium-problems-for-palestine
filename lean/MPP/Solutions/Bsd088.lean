import Mathlib

namespace MPP.Solutions.Bsd088

theorem main : ∀ (a : ℕ → ℂ) (s : ℂ), 3 / 2 < s.re →
    (∀ n : ℕ, 0 < n → ‖a n‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) →
    LSeriesSummable a s := by
  intro a s hs ha
  have hur : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
    simp only [Complex.sub_re, Complex.div_re]
    norm_num
  have hu : 1 < (s - 1 / 2 : ℂ).re := by
    rw [hur]
    linarith
  -- the divisor-count series at u = s - 1/2 (the content of bsd-087)
  have h1 : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) (s - 1 / 2) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => by simp) hu
  have hD : LSeriesSummable (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) (s - 1 / 2) := by
    have h2 := h1.convolution h1
    convert h2 using 2
    rename_i n
    rw [LSeries.convolution_def]
    dsimp only
    rw [← Nat.map_div_right_divisors, Finset.sum_map]
    simp
  have hD2 : Summable (fun n : ℕ => ‖LSeries.term (fun n : ℕ => ((n.divisors.card : ℕ) : ℂ)) (s - 1 / 2) n‖) :=
    summable_norm_iff.mpr hD
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hD2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hp : (0 : ℝ) < (n : ℝ) ^ (s - 1 / 2 : ℂ).re := Real.rpow_pos_of_pos hn' _
    have hpow : (n : ℝ) ^ s.re = (n : ℝ) ^ (s - 1 / 2 : ℂ).re * Real.sqrt n := by
      rw [hur, Real.sqrt_eq_rpow, ← Real.rpow_add hn']
      congr 1
      ring
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', norm_div, norm_div,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn, hpow,
      Complex.norm_natCast]
    rw [div_le_div_iff₀ (by positivity) hp]
    have hA := ha n hn
    calc ‖a n‖ * (n : ℝ) ^ (s - 1 / 2 : ℂ).re
        ≤ ((n.divisors.card : ℝ) * Real.sqrt n) * (n : ℝ) ^ (s - 1 / 2 : ℂ).re :=
          mul_le_mul_of_nonneg_right hA hp.le
      _ = (n.divisors.card : ℝ) * ((n : ℝ) ^ (s - 1 / 2 : ℂ).re * Real.sqrt n) := by ring

end MPP.Solutions.Bsd088
