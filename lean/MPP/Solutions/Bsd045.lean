import Mathlib
import MPP.Solutions.Bsd020
import MPP.Solutions.Bsd022
import MPP.Solutions.Bsd023

namespace MPP.Solutions.Bsd045

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    (∀ p k : ℕ, p.Prime →
      ‖((E.LFunction (p ^ k) : ℤ) : ℂ)‖ ≤ ((p ^ k).divisors.card : ℝ) * Real.sqrt ((p ^ k : ℕ) : ℝ)) →
    ∀ n : ℕ, 0 < n → ‖((E.LFunction n : ℤ) : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt (n : ℝ) := by
  intro E _ hpp n hn
  have hmul := MPP.Solutions.Bsd020.main E
  have hc1 : ‖((E.LFunction 1 : ℤ) : ℂ)‖ = 1 := by
    rw [hmul.map_one]
    simp
  have hf1 : ((Nat.divisors 1).card : ℝ) * Real.sqrt ((1 : ℕ) : ℝ) = 1 := by
    simp
  have hcmul : ∀ m k : ℕ, Nat.Coprime m k →
      ‖((E.LFunction (m * k) : ℤ) : ℂ)‖ = ‖((E.LFunction m : ℤ) : ℂ)‖ * ‖((E.LFunction k : ℤ) : ℂ)‖ := by
    intro m k hmk
    rw [hmul.map_mul_of_coprime hmk, Int.cast_mul, norm_mul]
  have hfmul : ∀ m k : ℕ, Nat.Coprime m k →
      ((m * k).divisors.card : ℝ) * Real.sqrt ((m * k : ℕ) : ℝ) =
        ((m.divisors.card : ℝ) * Real.sqrt (m : ℝ)) * ((k.divisors.card : ℝ) * Real.sqrt (k : ℝ)) := by
    intro m k hmk
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.coprime_zero_left] at hmk
      subst hmk
      simp
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Nat.coprime_zero_right] at hmk
      subst hmk
      simp
    exact MPP.Solutions.Bsd022.main m k hm hk hmk
  have hc := MPP.Solutions.Bsd023.main (fun n => ‖((E.LFunction n : ℤ) : ℂ)‖)
    (fun n => (n.divisors.card : ℝ) * Real.sqrt (n : ℝ)) hc1 hf1
    (fun m k hmk => hcmul m k hmk) (fun m k hmk => hfmul m k hmk)
    (fun p k _ => by positivity)
    (fun p k hp => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact hpp p k hp)
    n hn
  rwa [abs_of_nonneg (norm_nonneg _)] at hc

end MPP.Solutions.Bsd045
