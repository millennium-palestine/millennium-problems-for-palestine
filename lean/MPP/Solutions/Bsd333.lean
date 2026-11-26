import Mathlib

namespace MPP.Solutions.Bsd333

theorem main : ∀ (a b : ZMod 7), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∀ g : Polynomial (ZMod 7),
      g = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((7 - 1) / 2) →
      (Matrix.of (fun (i t : Fin ((7 - 1) / 2)) =>
        Polynomial.C (g.coeff ((7 - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((7 - 1) / 2 + (i : ℕ) - (t : ℕ) + 7)) * (Polynomial.X : Polynomial (ZMod 7)))).det ≠ 0 := by
  intro a b h g hg
  have hg' : g = Polynomial.X ^ 9 + Polynomial.C (3 * a) * Polynomial.X ^ 7 + Polynomial.C (3 * b) * Polynomial.X ^ 6
      + Polynomial.C (3 * a ^ 2) * Polynomial.X ^ 5 + Polynomial.C (6 * a * b) * Polynomial.X ^ 4
      + Polynomial.C (3 * b ^ 2 + a ^ 3) * Polynomial.X ^ 3 + Polynomial.C (3 * a ^ 2 * b) * Polynomial.X ^ 2
      + Polynomial.C (3 * a * b ^ 2) * Polynomial.X + Polynomial.C (b ^ 3) := by
    rw [hg]
    norm_num
    simp only [map_ofNat]
    ring
  have c1 : g.coeff 1 = 3 * a * b ^ 2 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c2 : g.coeff 2 = 3 * a ^ 2 * b := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c3 : g.coeff 3 = 3 * b ^ 2 + a ^ 3 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c4 : g.coeff 4 = 6 * a * b := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c5 : g.coeff 5 = 3 * a ^ 2 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c8 : g.coeff 8 = 0 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c9 : g.coeff 9 = 1 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c10 : g.coeff 10 = 0 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c11 : g.coeff 11 = 0 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c12 : g.coeff 12 = 0 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  erw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  norm_num [c1, c2, c3, c4, c5, c8, c9, c10, c11, c12]
  intro hdet
  have e0 := congrArg (Polynomial.eval 0) hdet
  have e1 := congrArg (Polynomial.eval 1) hdet
  have em := congrArg (Polynomial.eval (-1)) hdet
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_zero] at e0 e1 em
  have h6 : (6 : ZMod 7) * a ^ 2 = 0 := by linear_combination e1 + em - 2 * e0
  have ha : a = 0 := (by decide : ∀ x : ZMod 7, 6 * x ^ 2 = 0 → x = 0) a h6
  subst ha
  have hb6 : (27 : ZMod 7) * b ^ 6 = 0 := by linear_combination e0
  have hb : b = 0 := (by decide : ∀ x : ZMod 7, 27 * x ^ 6 = 0 → x = 0) b hb6
  apply h
  subst hb
  norm_num

end MPP.Solutions.Bsd333
