import Mathlib

namespace MPP.Solutions.Bsd164

theorem main : ∀ k : ℕ,
    PowerSeries.coeff k (PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1) = 1 ∧
    PowerSeries.coeff k (PowerSeries.invOfUnit (1 + PowerSeries.X : PowerSeries ℤ) 1) = (-1) ^ k := by
  intro k
  set gA := PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 with hgA
  set gB := PowerSeries.invOfUnit (1 + PowerSeries.X : PowerSeries ℤ) 1 with hgB
  have hA : (1 - PowerSeries.X : PowerSeries ℤ) * gA = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have hB : (1 + PowerSeries.X : PowerSeries ℤ) * gB = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have A : ∀ n : ℕ, PowerSeries.coeff n gA = 1 := by
    intro n
    induction n with
    | zero =>
      have := congrArg (PowerSeries.coeff 0) hA
      simpa [sub_mul, PowerSeries.coeff_zero_X_mul] using this
    | succ n ih =>
      have := congrArg (PowerSeries.coeff (n + 1)) hA
      simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at this
      simp only [Nat.succ_ne_zero, if_false] at this
      linarith
  have B : ∀ n : ℕ, PowerSeries.coeff n gB = (-1) ^ n := by
    intro n
    induction n with
    | zero =>
      have := congrArg (PowerSeries.coeff 0) hB
      simpa [add_mul, PowerSeries.coeff_zero_X_mul] using this
    | succ n ih =>
      have := congrArg (PowerSeries.coeff (n + 1)) hB
      simp only [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at this
      simp only [Nat.succ_ne_zero, if_false] at this
      rw [pow_succ]
      linarith
  exact ⟨A k, B k⟩

end MPP.Solutions.Bsd164
