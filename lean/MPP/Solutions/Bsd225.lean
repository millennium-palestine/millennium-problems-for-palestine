import Mathlib

namespace MPP.Solutions.Bsd225

/-! Nonvanishing of the universal `normEDS`. The transfer to a curve over ℚ maps the universal
value to `W.ψ k`; the odd case uses that `W.preΨ k` has leading coefficient `k`, and the even case
uses the same leading coefficient together with the factor `ψ₂ = 2y + a₁x + a₃`. In both cases a
nonzero polynomial in `x` times, or equal to, `ψ₂` cannot be a multiple of the monic quadratic
Weierstrass polynomial, by a degree count in `y`. -/

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

/-- The transfer: a vanishing universal value at `k` gives `W.ψ k = 0` on the test curve. -/
lemma transfer_psi (k : ℤ) (hzero : normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) k = 0) :
    (⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve ℚ).ψ k = 0 := by
  have hf := congrArg (MvPolynomial.aeval
    ![(⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve ℚ).ψ₂, Polynomial.C (⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve ℚ).Ψ₃,
      Polynomial.C (⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve ℚ).preΨ₄] :
      MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial ℚ)) hzero
  simp only [map_zero, map_normEDS, MvPolynomial.aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hf
  exact hf

lemma odd_case (k : ℤ) (hk : Odd k) (hzero : normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) k = 0) : False := by
  have hk0' : k ≠ 0 := by
    rintro rfl
    norm_num at hk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0'
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 1⟩
  have hpsi : W.ψ k = 0 := transfer_psi k hzero
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

lemma even_case (k : ℤ) (hk : Even k) (hk00 : k ≠ 0) (hzero : normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) k = 0) : False := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk00
  let W : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 1⟩
  have hpsi : W.ψ k = 0 := transfer_psi k hzero
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

theorem main : ∀ k : ℤ, k ≠ 0 →
    normEDS (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) (MvPolynomial.X 2) k ≠ 0 := by
  intro k hk00 hzero
  rcases Int.even_or_odd k with he | ho
  · exact even_case k he hk00 hzero
  · exact odd_case k ho hzero

end MPP.Solutions.Bsd225
