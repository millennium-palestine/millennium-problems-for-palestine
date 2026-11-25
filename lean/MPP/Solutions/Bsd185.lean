import Mathlib

namespace MPP.Solutions.Bsd185

theorem main : ∀ (c : ℕ → ℝ) (K ε σ : ℝ), 0 < ε → 1 < σ - 1 / 2 - ε →
    (∀ n : ℕ, 1 ≤ n → |c n| ≤ K * (n : ℝ) ^ (1 / 2 + ε)) →
    Summable (fun n : ℕ => c n / (n : ℝ) ^ σ) := by
  intro c K ε σ hε hσ hc
  have he : 1 / 2 + ε - σ < -1 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (1 / 2 + ε - σ)) :=
    Real.summable_nat_rpow.mpr he
  refine Summable.of_norm_bounded (hsum.mul_left |K|) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hσ0 : σ ≠ 0 := by intro h; linarith
    have he0 : 1 / 2 + ε - σ ≠ 0 := by intro h; linarith
    rw [Nat.cast_zero, Real.zero_rpow hσ0, div_zero, norm_zero, Real.zero_rpow he0, mul_zero]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hσpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
    have h2 : (n : ℝ) ^ (1 / 2 + ε - σ) * (n : ℝ) ^ σ = (n : ℝ) ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add hnpos]
      ring_nf
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hσpos, div_le_iff₀ hσpos]
    calc |c n| ≤ K * (n : ℝ) ^ (1 / 2 + ε) := hc n hn
      _ ≤ |K| * (n : ℝ) ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hnpos.le _)
      _ = |K| * ((n : ℝ) ^ (1 / 2 + ε - σ) * (n : ℝ) ^ σ) := by rw [h2]
      _ = |K| * (n : ℝ) ^ (1 / 2 + ε - σ) * (n : ℝ) ^ σ := by ring

end MPP.Solutions.Bsd185
