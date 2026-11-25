import Mathlib

namespace MPP.Solutions.Bsd163

open PowerSeries

theorem main : ∀ a q : ℤ,
    PowerSeries.coeff 0 (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1) = 1 ∧
    PowerSeries.coeff 1 (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1) = a ∧
    ∀ k : ℕ, PowerSeries.coeff (k + 2) (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1) =
      a * PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1) -
        q * PowerSeries.coeff k (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1) := by
  intro a q
  set g := PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) 1 with hgdef
  have hg : (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2) * g = 1 := by
    apply PowerSeries.mul_invOfUnit
    simp
  have hexp : g - PowerSeries.C a * (PowerSeries.X * g) +
      PowerSeries.C q * (PowerSeries.X * (PowerSeries.X * g)) = 1 := by
    linear_combination hg
  have c : ∀ n : ℕ, PowerSeries.coeff n g - a * PowerSeries.coeff n (PowerSeries.X * g) +
      q * PowerSeries.coeff n (PowerSeries.X * (PowerSeries.X * g)) =
      PowerSeries.coeff n (1 : PowerSeries ℤ) := by
    intro n
    have := congrArg (PowerSeries.coeff n) hexp
    rw [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at this
    exact this
  have f0 : PowerSeries.coeff 0 (PowerSeries.X * g) = 0 := PowerSeries.coeff_zero_X_mul g
  have e0 : PowerSeries.coeff 0 (PowerSeries.X * (PowerSeries.X * g)) = 0 :=
    PowerSeries.coeff_zero_X_mul _
  have f1 : PowerSeries.coeff 1 (PowerSeries.X * g) = PowerSeries.coeff 0 g :=
    PowerSeries.coeff_succ_X_mul 0 g
  have e1 : PowerSeries.coeff 1 (PowerSeries.X * (PowerSeries.X * g)) = PowerSeries.coeff 0 (PowerSeries.X * g) :=
    PowerSeries.coeff_succ_X_mul 0 _
  have h0 : PowerSeries.coeff 0 g = 1 := by
    have := c 0
    simpa [f0, e0, PowerSeries.coeff_one] using this
  have h1 : PowerSeries.coeff 1 g = a := by
    have := c 1
    simp only [f1, e1, f0, h0, PowerSeries.coeff_one] at this
    norm_num at this
    linarith
  refine ⟨h0, h1, fun k => ?_⟩
  have hk := c (k + 2)
  have s1 : PowerSeries.coeff (k + 2) (PowerSeries.X * g) = PowerSeries.coeff (k + 1) g :=
    PowerSeries.coeff_succ_X_mul (k + 1) g
  have s2 : PowerSeries.coeff (k + 2) (PowerSeries.X * (PowerSeries.X * g)) = PowerSeries.coeff k g := by
    rw [PowerSeries.coeff_succ_X_mul (k + 1) (PowerSeries.X * g), PowerSeries.coeff_succ_X_mul k g]
  have s3 : PowerSeries.coeff (k + 2) (1 : PowerSeries ℤ) = 0 := by
    simp [PowerSeries.coeff_one]
  rw [s1, s2, s3] at hk
  linarith

end MPP.Solutions.Bsd163
