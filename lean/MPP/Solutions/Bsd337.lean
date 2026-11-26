import Mathlib

namespace MPP.Solutions.Bsd337

theorem fin11_det : ∀ a b : ZMod 11, 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 → ∃ y : ZMod 11,
    Matrix.det !![(a^5 + 30*a^2*b^2) + (0) * y, (5*a^4*b + 20*a*b^3) + (1) * y, (10*a^3*b^2 + 5*b^4) + (0) * y, (10*a^2*b^3) + (5*a) * y, (5*a*b^4) + (5*b) * y;
    (20*a^3*b + 10*b^3) + (0) * y, (a^5 + 30*a^2*b^2) + (0) * y, (5*a^4*b + 20*a*b^3) + (1) * y, (10*a^3*b^2 + 5*b^4) + (0) * y, (10*a^2*b^3) + (5*a) * y;
    (5*a^4 + 30*a*b^2) + (0) * y, (20*a^3*b + 10*b^3) + (0) * y, (a^5 + 30*a^2*b^2) + (0) * y, (5*a^4*b + 20*a*b^3) + (1) * y, (10*a^3*b^2 + 5*b^4) + (0) * y;
    (30*a^2*b) + (0) * y, (5*a^4 + 30*a*b^2) + (0) * y, (20*a^3*b + 10*b^3) + (0) * y, (a^5 + 30*a^2*b^2) + (0) * y, (5*a^4*b + 20*a*b^3) + (1) * y;
    (10*a^3 + 10*b^2) + (0) * y, (30*a^2*b) + (0) * y, (5*a^4 + 30*a*b^2) + (0) * y, (20*a^3*b + 10*b^3) + (0) * y, (a^5 + 30*a^2*b^2) + (0) * y] ≠ 0 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem main : ∀ (a b : ZMod 11), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∀ g : Polynomial (ZMod 11),
      g = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((11 - 1) / 2) →
      (Matrix.of (fun (i t : Fin ((11 - 1) / 2)) =>
        Polynomial.C (g.coeff ((11 - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((11 - 1) / 2 + (i : ℕ) - (t : ℕ) + 11)) * (Polynomial.X : Polynomial (ZMod 11)))).det ≠ 0 := by
  intro a b h g hg
  have hg' : g = Polynomial.C (b ^ 5) + Polynomial.C (5 * a * b ^ 4) * Polynomial.X
      + Polynomial.C (10 * a ^ 2 * b ^ 3) * Polynomial.X ^ 2
      + Polynomial.C (10 * a ^ 3 * b ^ 2 + 5 * b ^ 4) * Polynomial.X ^ 3
      + Polynomial.C (5 * a ^ 4 * b + 20 * a * b ^ 3) * Polynomial.X ^ 4
      + Polynomial.C (a ^ 5 + 30 * a ^ 2 * b ^ 2) * Polynomial.X ^ 5
      + Polynomial.C (20 * a ^ 3 * b + 10 * b ^ 3) * Polynomial.X ^ 6
      + Polynomial.C (5 * a ^ 4 + 30 * a * b ^ 2) * Polynomial.X ^ 7
      + Polynomial.C (30 * a ^ 2 * b) * Polynomial.X ^ 8
      + Polynomial.C (10 * a ^ 3 + 10 * b ^ 2) * Polynomial.X ^ 9
      + Polynomial.C (20 * a * b) * Polynomial.X ^ 10
      + Polynomial.C (10 * a ^ 2) * Polynomial.X ^ 11
      + Polynomial.C (5 * b) * Polynomial.X ^ 12
      + Polynomial.C (5 * a) * Polynomial.X ^ 13
      + Polynomial.X ^ 15 := by
    rw [hg]
    norm_num
    simp only [map_ofNat]
    ring
  have hdeg : g.natDegree ≤ 15 := by
    have hK : (11 - 1) / 2 = 5 := by norm_num
    rw [hg, hK]
    have h3 : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod 11)).natDegree ≤ 3 := by
      compute_degree!
    have h5 := Polynomial.natDegree_pow_le (p := (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod 11))) (n := 5)
    omega
  have hz : ∀ m : ℕ, 15 < m → g.coeff m = 0 := fun m hm =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have c1 : g.coeff 1 = 5 * a * b ^ 4 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c2 : g.coeff 2 = 10 * a ^ 2 * b ^ 3 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c3 : g.coeff 3 = 10 * a ^ 3 * b ^ 2 + 5 * b ^ 4 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c4 : g.coeff 4 = 5 * a ^ 4 * b + 20 * a * b ^ 3 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c5 : g.coeff 5 = a ^ 5 + 30 * a ^ 2 * b ^ 2 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c6 : g.coeff 6 = 20 * a ^ 3 * b + 10 * b ^ 3 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c7 : g.coeff 7 = 5 * a ^ 4 + 30 * a * b ^ 2 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c8 : g.coeff 8 = 30 * a ^ 2 * b := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c9 : g.coeff 9 = 10 * a ^ 3 + 10 * b ^ 2 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c12 : g.coeff 12 = 5 * b := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c13 : g.coeff 13 = 5 * a := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c14 : g.coeff 14 = 0 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  have c15 : g.coeff 15 = 1 := by
    rw [hg']; simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, Polynomial.coeff_X_pow]
    norm_num
  obtain ⟨y0, hy0⟩ := fin11_det a b h
  intro hdet
  have hev := congrArg (Polynomial.eval y0) hdet
  rw [Polynomial.eval_zero] at hev
  have h2 := RingHom.map_det (Polynomial.evalRingHom y0) (Matrix.of fun (i t : Fin ((11 - 1) / 2)) =>
        Polynomial.C (g.coeff ((11 - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((11 - 1) / 2 + (i : ℕ) - (t : ℕ) + 11)) * (Polynomial.X : Polynomial (ZMod 11)))
  change Polynomial.eval y0 _ = _ at h2
  rw [h2] at hev
  apply hy0
  convert hev using 2
  ext i t
  fin_cases i <;> fin_cases t <;> simp [c1, c2, c3, c4, c5, c6, c7, c8, c9, c12, c13, c14, c15, hz]

end MPP.Solutions.Bsd337
