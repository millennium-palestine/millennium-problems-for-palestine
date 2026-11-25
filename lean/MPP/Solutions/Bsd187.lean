import Mathlib

namespace MPP.Solutions.Bsd187

theorem main : ∀ σ : ℝ, 3 / 2 < σ →
    Summable (fun p : ℕ => if p.Prime then (p : ℝ) ^ (1 / 2 - σ) else 0) := by
  intro σ hσ
  have hexp : 1 / 2 - σ < -1 := by linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (Real.summable_nat_rpow.mpr hexp)
  · split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_refl _
  · split_ifs with h
    · exact le_refl _
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

end MPP.Solutions.Bsd187
