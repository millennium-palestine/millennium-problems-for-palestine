import Mathlib

namespace MPP.Solutions.Bsd292

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod p)),
    (∀ i t : Fin (n + 1), t ≤ i → N i t = 0) →
    (∀ i : Fin n, N (Fin.castSucc i) (Fin.succ i) = 1) →
    (Matrix.of (fun i t : Fin (n + 1) =>
      (Polynomial.C (M i t) + Polynomial.X * Polynomial.C (N i t) : Polynomial (ZMod p)))).det.coeff n =
      (-1) ^ n * M (Fin.last n) 0 := by
  intro p _ n M N hlow hsup
  have hA : Matrix.of (fun i t : Fin (n + 1) =>
      (Polynomial.C (M i t) + Polynomial.X * Polynomial.C (N i t) : Polynomial (ZMod p))) =
      (Polynomial.X : Polynomial (ZMod p)) • N.map Polynomial.C + M.map Polynomial.C := by
    refine Matrix.ext fun i t => ?_
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    ring
  have hminor : ∀ i : Fin (n + 1),
      ((Polynomial.X : Polynomial (ZMod p)) • N.map Polynomial.C + M.map Polynomial.C).submatrix
        i.succAbove Fin.succ =
      (Polynomial.X : Polynomial (ZMod p)) • ((N.submatrix i.succAbove Fin.succ).map Polynomial.C) +
        (M.submatrix i.succAbove Fin.succ).map Polynomial.C := by
    intro i
    refine Matrix.ext fun r c => ?_
    simp
  have hcol : ∀ i : Fin (n + 1),
      ((Polynomial.X : Polynomial (ZMod p)) • N.map Polynomial.C + M.map Polynomial.C) i 0 =
        Polynomial.C (M i 0) := by
    intro i
    simp [hlow i 0 (Fin.zero_le i)]
  -- entries of N in the minor deleting row i, column 0
  have hD : ∀ i : Fin (n + 1), i ≠ Fin.last n → (N.submatrix i.succAbove Fin.succ).det = 0 := by
    intro i hi
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
    refine Matrix.det_eq_zero_of_row_eq_zero z fun c => ?_
    simp only [Matrix.submatrix_apply]
    rw [hz]
    exact hlow (Fin.last n) _ (Fin.le_last _)
  -- the minor deleting the last row is unit upper triangular
  have hdet1 : (N.submatrix (Fin.last n).succAbove Fin.succ).det = 1 := by
    rw [Fin.succAbove_last]
    rw [Matrix.det_of_upperTriangular]
    · simp [hsup]
    · intro i j hji
      simp only [Matrix.submatrix_apply]
      exact hlow _ _ (Fin.succ_le_castSucc_iff.mpr hji)
  have key : ∀ i : Fin (n + 1),
      (((-1 : Polynomial (ZMod p)) ^ (i : ℕ)) *
        (((Polynomial.X : Polynomial (ZMod p)) • N.map Polynomial.C + M.map Polynomial.C) i 0) *
        Matrix.det (((Polynomial.X : Polynomial (ZMod p)) • N.map Polynomial.C + M.map Polynomial.C).submatrix
          i.succAbove Fin.succ)).coeff n =
        (-1) ^ (i : ℕ) * M i 0 * (N.submatrix i.succAbove Fin.succ).det := by
    intro i
    have h1 := coeff_det_X_add_C_card (N.submatrix i.succAbove Fin.succ) (M.submatrix i.succAbove Fin.succ)
    rw [Fintype.card_fin] at h1
    have hC : ((-1 : Polynomial (ZMod p)) ^ (i : ℕ)) = Polynomial.C ((-1) ^ (i : ℕ)) := by simp
    rw [hcol, hminor, hC, ← Polynomial.C_mul, Polynomial.coeff_C_mul, h1]
  rw [hA, Matrix.det_succ_column_zero, Polynomial.finsetSum_coeff]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_eq_single (Fin.last n)]
  · rw [Fin.val_last, hdet1, mul_one]
  · intro i _ hi
    rw [hD i hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end MPP.Solutions.Bsd292
