import Mathlib

namespace MPP.Solutions.Bsd227

theorem main : ∀ k : ℤ, Odd k →
    normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) (MvPolynomial.X 2) k ≠ 0 := by
  intro k hk hzero
  have hk0' : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0'
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 1⟩
  have hf := congrArg (MvPolynomial.aeval
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄] :
      MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial ℚ)) hzero
  simp only [map_zero, map_normEDS, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hf
  have hpsi : W.ψ k = 0 := hf
  have hΨ : W.Ψ k = Polynomial.C (W.preΨ k) := by
    simp [WeierstrassCurve.Ψ, Int.not_even_iff_odd.mpr hk]
  have hlc : (W.preΨ k).leadingCoeff = k := by
    rw [WeierstrassCurve.leadingCoeff_preΨ (W := W) (by exact_mod_cast hk0)]
    simp [Int.not_even_iff_odd.mpr hk]
  have hne : W.preΨ k ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hlc
    exact hk0 (by exact_mod_cast hlc.symm)
  have hdvd : W.toAffine.polynomial ∣ Polynomial.C (W.preΨ k) := by
    have hm := WeierstrassCurve.Affine.CoordinateRing.mk_ψ (W := W) k
    rw [hΨ, hpsi, map_zero] at hm
    exact AdjoinRoot.mk_eq_zero.mp hm.symm
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hne
    rw [mul_zero] at hg
    exact Polynomial.C_eq_zero.mp hg
  have hdeg := congrArg Polynomial.natDegree hg
  rw [Polynomial.natDegree_mul W.toAffine.monic_polynomial.ne_zero hg0, Polynomial.natDegree_C,
    W.toAffine.natDegree_polynomial] at hdeg
  omega

end MPP.Solutions.Bsd227
