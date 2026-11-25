import Mathlib

namespace MPP.Solutions.Bsd228

lemma not_dvd_of_natDegree_lt_two (W : WeierstrassCurve ℚ) {g : Polynomial (Polynomial ℚ)}
    (hg : g ≠ 0) (hdeg : g.natDegree < 2) : ¬ W.toAffine.polynomial ∣ g := by
  rintro ⟨h, rfl⟩
  have hh : h ≠ 0 := by
    rintro rfl
    exact hg (mul_zero _)
  rw [Polynomial.natDegree_mul W.toAffine.monic_polynomial.ne_zero hh,
    W.toAffine.natDegree_polynomial] at hdeg
  omega

lemma psi2_ne_zero (W : WeierstrassCurve ℚ) : W.ψ₂ ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial (Polynomial ℚ) => p.coeff 1) h
  simp [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY] at h2

lemma psi2_natDegree_lt (W : WeierstrassCurve ℚ) : W.ψ₂.natDegree < 2 := by
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY
  compute_degree!

theorem main : ∀ k : ℤ, Even k → k ≠ 0 →
    normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) (MvPolynomial.X 2) k ≠ 0 := by
  intro k hk hk00 hzero
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk00
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 1⟩
  have hf := congrArg (MvPolynomial.aeval
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄] :
      MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial ℚ)) hzero
  simp only [map_zero, map_normEDS, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hf
  have hpsi : W.ψ k = 0 := hf
  have hΨ : W.Ψ k = Polynomial.C (W.preΨ k) * W.ψ₂ := by
    simp [WeierstrassCurve.Ψ, hk]
  have hlc : (W.preΨ k).leadingCoeff = ((k / 2 : ℤ) : ℚ) := by
    rw [WeierstrassCurve.leadingCoeff_preΨ (W := W) (by exact_mod_cast hk0)]
    simp [hk]
  have hne : W.preΨ k ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hlc
    have h1 : k / 2 = 0 := by exact_mod_cast hlc.symm
    obtain ⟨j, rfl⟩ := hk
    omega
  have hm := WeierstrassCurve.Affine.CoordinateRing.mk_ψ (W := W) k
  rw [hΨ, hpsi, map_zero, map_mul] at hm
  rcases mul_eq_zero.mp hm.symm with h1 | h2
  · have hC : Polynomial.C (W.preΨ k) ≠ 0 := fun h => hne (Polynomial.C_eq_zero.mp h)
    have hdeg : (Polynomial.C (W.preΨ k)).natDegree < 2 := by
      rw [Polynomial.natDegree_C]
      norm_num
    exact absurd (AdjoinRoot.mk_eq_zero.mp h1) (not_dvd_of_natDegree_lt_two W hC hdeg)
  · exact absurd (AdjoinRoot.mk_eq_zero.mp h2)
      (not_dvd_of_natDegree_lt_two W (psi2_ne_zero W) (psi2_natDegree_lt W))

end MPP.Solutions.Bsd228
