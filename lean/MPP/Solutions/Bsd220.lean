import Mathlib

namespace MPP.Solutions.Bsd220

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
    (x y : K) (h : W.toAffine.Nonsingular x y),
    (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (W.preΨ' 3).eval x = 0 := by
  intro K _ _ W _ x y h h3
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have e3 : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      ((WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)) +
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
    rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul, two_zsmul]
  have h2 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      -(WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
    rw [e3] at h3
    exact eq_neg_of_add_eq_zero_left h3
  by_cases hy : y = W.toAffine.negY x y
  · exfalso
    apply WeierstrassCurve.Affine.Point.some_ne_zero h
    apply neg_eq_zero.mp
    rw [← h2, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
      WeierstrassCurve.Affine.Point.neg_some] at h2
    have hx := (WeierstrassCurve.Affine.Point.some.inj h2).1
    obtain ⟨N, hN⟩ : ∃ N : K, N = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : K, D = y - W.toAffine.negY x y := ⟨_, rfl⟩
    have hD0 : D ≠ 0 := by
      rw [hD]
      exact sub_ne_zero.mpr hy
    have hslope : W.toAffine.slope x x y y = N / D := by
      rw [hN, hD]
      exact WeierstrassCurve.Affine.slope_of_Y_ne rfl hy
    rw [hslope] at hx
    have hx' : (N / D) ^ 2 + W.a₁ * (N / D) - W.a₂ - x - x = x := hx
    have eND : N / D * D = N := div_mul_cancel₀ N hD0
    have hH : N ^ 2 + W.a₁ * N * D - (W.a₂ + 3 * x) * D ^ 2 = 0 := by
      linear_combination D ^ 2 * hx' - (N + N / D * D + W.a₁ * D) * eND
    have hD' : D = 2 * y + W.a₁ * x + W.a₃ := by
      rw [hD, WeierstrassCurve.Affine.negY]
      ring
    rw [hN, hD'] at hH
    rw [W.preΨ'_three]
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-(W.a₁ ^ 2) - 4 * W.a₂ - 12 * x) * hE - hH

end MPP.Solutions.Bsd220
