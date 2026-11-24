import Mathlib

namespace MPP.Solutions.Bsd097

theorem main : ∀ (q p k : ℕ) (f : PowerSeries ℤ), 1 < q → p.Prime → ¬ p ∣ q → 0 < k →
    ArithmeticFunction.ofPowerSeries q f (p ^ k) = 0 := by
  intro q p k f hq hp hpq hk
  rw [ArithmeticFunction.ofPowerSeries_apply hq, Function.extend_apply' _ _ _ ?_, Pi.zero_apply]
  rintro ⟨j, hj⟩
  have h : p ∣ q ^ j := by
    rw [hj]
    exact dvd_pow_self p (by omega)
  exact hpq (hp.dvd_of_dvd_pow h)

end MPP.Solutions.Bsd097
