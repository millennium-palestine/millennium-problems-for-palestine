import Mathlib

namespace MPP.Solutions.Bsd096

theorem main : ∀ (q p k : ℕ) (f : PowerSeries ℤ), q.Prime → p.Prime → q ≠ p → 0 < k →
    ArithmeticFunction.ofPowerSeries q f (p ^ k) = 0 := by
  intro q p k f hq hp hqp hk
  rw [ArithmeticFunction.ofPowerSeries_apply hq.one_lt, Function.extend_apply' _ _ _ ?_, Pi.zero_apply]
  rintro ⟨j, hj⟩
  have hpq : p ∣ q := by
    have h : p ∣ q ^ j := by
      rw [hj]
      exact dvd_pow_self p (by omega)
    exact hp.dvd_of_dvd_pow h
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm

end MPP.Solutions.Bsd096
