import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp012

open MPP.PvsNP

theorem main : ∀ x w : List Bool, (pair x w).length = 2 * x.length + 2 + w.length := by
  intro x w
  induction x with
  | nil => simp [pair]; omega
  | cons b x ih =>
    have h : pair (b :: x) w = b :: b :: pair x w := by simp [pair]
    rw [h]
    simp only [List.length_cons, ih]
    omega

end MPP.Solutions.Pnp012
