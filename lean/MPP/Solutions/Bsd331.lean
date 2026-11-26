import Mathlib

namespace MPP.Solutions.Bsd331

theorem main : ∀ (a b : ZMod 5), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∀ g : Polynomial (ZMod 5),
      g = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((5 - 1) / 2) →
      (Matrix.of (fun (i t : Fin ((5 - 1) / 2)) =>
        Polynomial.C (g.coeff ((5 - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((5 - 1) / 2 + (i : ℕ) - (t : ℕ) + 5)) * (Polynomial.X : Polynomial (ZMod 5)))).det ≠ 0 := by
  intro a b h g hg
  have hsq : g = Polynomial.X ^ 6 + Polynomial.C (2 * a) * Polynomial.X ^ 4 + Polynomial.C (2 * b) * Polynomial.X ^ 3
        + Polynomial.C (a ^ 2) * Polynomial.X ^ 2 + Polynomial.C (2 * a * b) * Polynomial.X + Polynomial.C (b ^ 2) := by
    rw [hg]
    norm_num
    simp only [map_mul, map_ofNat]
    ring
  have c1 : g.coeff 1 = 2 * a * b := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c2 : g.coeff 2 = a ^ 2 := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c3 : g.coeff 3 = 2 * b := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c6 : g.coeff 6 = 1 := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c7 : g.coeff 7 = 0 := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c8 : g.coeff 8 = 0 := by
    rw [hsq]; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  erw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  norm_num [c1, c2, c3, c6, c7, c8]
  intro hdet
  have e0 := congrArg (Polynomial.eval 0) hdet
  have e1 := congrArg (Polynomial.eval 1) hdet
  simp at e0 e1
  have hb2 : (2 : ZMod 5) * b = 0 := by linear_combination e0 - e1
  have hb : b = 0 := (by decide : ∀ x : ZMod 5, 2 * x = 0 → x = 0) b hb2
  subst hb
  have ha4 : a ^ 4 = 0 := by linear_combination e0
  have ha : a = 0 := (by decide : ∀ x : ZMod 5, x ^ 4 = 0 → x = 0) a ha4
  apply h
  subst ha
  norm_num

end MPP.Solutions.Bsd331
