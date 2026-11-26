import Mathlib

namespace MPP.Solutions.Bsd330

theorem main : ∀ (a b : ZMod 3), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∀ g : Polynomial (ZMod 3),
      g = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((3 - 1) / 2) →
      (Matrix.of (fun (i t : Fin ((3 - 1) / 2)) =>
        Polynomial.C (g.coeff ((3 - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((3 - 1) / 2 + (i : ℕ) - (t : ℕ) + 3)) * (Polynomial.X : Polynomial (ZMod 3)))).det ≠ 0 := by
  intro a b h g hg
  have ha : a ≠ 0 := by
    intro ha
    apply h
    subst ha
    exact (by decide : ∀ x : ZMod 3, (4 * (0 : ZMod 3) ^ 3 + 27 * x ^ 2) = 0) b
  subst hg
  erw [Matrix.det_fin_one]
  simp only [Matrix.of_apply]
  norm_num
  exact ha

end MPP.Solutions.Bsd330
