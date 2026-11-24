import Mathlib
import MPP.Solutions.Bsd028

namespace MPP.Solutions.Bsd033

theorem main : ∀ (a q : ℤ), 0 ≤ q → a ^ 2 ≤ 4 * q → ∀ k : ℕ,
    (PowerSeries.coeff k (PowerSeries.invOfUnit ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) 1)) ^ 2 ≤ ((k : ℤ) + 1) ^ 2 * q ^ k := by
  intro a q hq ha k
  set f : PowerSeries ℤ := ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) with hf
  set g : PowerSeries ℤ := PowerSeries.invOfUnit f 1 with hg
  have hf' : f = 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2 := by
    rw [hf]
    push_cast
    rfl
  have hmul : f * g = 1 := PowerSeries.mul_invOfUnit f 1 (by simp [hf])
  have hfg : g - PowerSeries.C a * (PowerSeries.X * g) + PowerSeries.C q * (PowerSeries.X * (PowerSeries.X * g)) = 1 := by
    rw [← hmul, hf']
    ring
  have hrec : ∀ n : ℕ, PowerSeries.coeff (n + 2) g = a * PowerSeries.coeff (n + 1) g - q * PowerSeries.coeff n g := by
    intro n
    have h := congrArg (PowerSeries.coeff (n + 2)) hfg
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one] at h
    simp at h
    linarith
  have h0 : PowerSeries.coeff 0 g = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hfg
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_one] at h
    simpa using h
  have h1 : PowerSeries.coeff 1 g = a := by
    have h := congrArg (PowerSeries.coeff 1) hfg
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_one] at h
    simp at h
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
    rw [h0, mul_one] at h
    linarith
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have ha' : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ) := by exact_mod_cast ha
  have hrec' : ∀ n : ℕ, ((PowerSeries.coeff (n + 2) g : ℤ) : ℝ) =
      (a : ℝ) * ((PowerSeries.coeff (n + 1) g : ℤ) : ℝ) - (q : ℝ) * ((PowerSeries.coeff n g : ℤ) : ℝ) := by
    intro n
    rw [hrec n]
    push_cast
    ring
  have hreal := MPP.Solutions.Bsd028.main (a : ℝ) (q : ℝ) (fun n => ((PowerSeries.coeff n g : ℤ) : ℝ))
    hq0 ha' (by simp [h0]) (by simp [h1]) hrec'
    k
  have hB := pow_le_pow_left₀ (abs_nonneg _) hreal 2
  rw [sq_abs, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt hq0] at hB
  have hfinal : ((PowerSeries.coeff k g : ℤ) : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * (q : ℝ) ^ k := hB
  exact_mod_cast hfinal

end MPP.Solutions.Bsd033
