import Mathlib

namespace MPP.Solutions.Bsd264

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y x3 y3 : K)
  (h : W.toAffine.Nonsingular x y) (h3 : W.toAffine.Nonsingular x3 y3),
  2 * y + W.a₁ * x + W.a₃ ≠ 0 →
  (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
    WeierstrassCurve.Affine.Point.some x3 y3 h3 →
  x3 * (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 2 =
    x * (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 2 -
      (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) *
        (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) := by
  intro K _ _ W x y x3 y3 h h3 hD h3P
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hD' : y - W.toAffine.negY x y = (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hD
    rw [← hD']
    exact sub_eq_zero.mpr hy
  have hL0 : W.toAffine.slope x x y y = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne, hD']
  obtain ⟨x2, y2, h2, hPP⟩ : ∃ (x2 y2 : K) (h2 : W.toAffine.Nonsingular x2 y2),
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x2 y2 h2 :=
    ⟨_, _, _, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne⟩
  have hx2e : x2 = W.toAffine.addX x x (W.toAffine.slope x x y y) ∧
      y2 = W.toAffine.addY x x y (W.toAffine.slope x x y y) := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne] at hPP
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hPP
    exact ⟨hPP.1.symm, hPP.2.symm⟩
  have hxne : x ≠ x2 := by
    intro hxx
    rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp hxx with hA | hA
    · have e0 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
          WeierstrassCurve.Affine.Point.some x y h =
          WeierstrassCurve.Affine.Point.some x y h + 0 := by
        rw [hPP, ← hA, add_zero]
      exact WeierstrassCurve.Affine.Point.some_ne_zero h (add_left_cancel e0)
    · have hQ : (WeierstrassCurve.Affine.Point.some x2 y2 h2 : W.toAffine.Point) =
          -WeierstrassCurve.Affine.Point.some x y h := by
        rw [hA, neg_neg]
      have e3 : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some x y h +
            (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) := by
        abel
      apply WeierstrassCurve.Affine.Point.some_ne_zero h3
      rw [← h3P, e3, hPP, hQ, add_neg_cancel]
  have e3 : (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x2 y2 h2 := by
    rw [← hPP]
    abel
  rw [e3, WeierstrassCurve.Affine.Point.add_of_X_ne hxne] at h3P
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at h3P
  obtain ⟨hx3e, -⟩ := h3P
  have hℓ : W.toAffine.slope x x2 y y2 * (x - x2) = y - y2 := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
    exact div_mul_cancel₀ (y - y2) (sub_ne_zero.mpr hxne)
  generalize hℓg : W.toAffine.slope x x2 y y2 = ℓ at hℓ hx3e
  have hx3' : x3 = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x - x2 := by
    rw [← hx3e]
    rfl
  generalize hsg : W.toAffine.slope x x y y = s at hL0 hx2e
  have hs : s * (2 * y + W.a₁ * x + W.a₃) = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) := by
    rw [hL0]
    exact div_mul_cancel₀ _ hD
  have hx2 : x2 = s ^ 2 + W.a₁ * s - W.a₂ - 2 * x := by
    rw [hx2e.1]
    simp only [WeierstrassCurve.Affine.addX]
    ring
  have hy2 : y2 = -(s * (x2 - x) + y) - W.a₁ * x2 - W.a₃ := by
    rw [hx2e.2]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, ← hx2e.1]
  have hu : (2 * y + W.a₁ * x + W.a₃) ^ 2 = (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) := by
    linear_combination 4 * hE
  have hx2F : x2 * (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) = (x ^ 4 - (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 - 2 * (W.a₃ ^ 2 + 4 * W.a₆) * x - (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2)) := by
    linear_combination (-x2) * hu + (2 * y + W.a₁ * x + W.a₃) ^ 2 * hx2 + (s * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hs +
      (-(W.a₁ ^ 2 + 4 * W.a₂ + 8 * x)) * hE
  have hwF : (x2 - x) * (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) = -(3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 + 3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 + 3 * (W.a₃ ^ 2 + 4 * W.a₆) * x + (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2)) := by
    linear_combination hx2F
  have hG : ℓ * (x2 - x) + (s + W.a₁) * (x2 - x) + (2 * y + W.a₁ * x + W.a₃) = 0 := by
    linear_combination hy2 - hℓ
  have hH : (x2 - x) ^ 2 * (x3 - x) = (6 * x ^ 2 + 4 * W.a₂ * x + 2 * W.a₄ + W.a₁ ^ 2 * x + W.a₁ * W.a₃) * (x2 - x) + (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination ((x2 - x) ^ 2) * hx3' + (ℓ * (x2 - x) - (s + W.a₁) * (x2 - x) - (2 * y + W.a₁ * x + W.a₃) + W.a₁ * (x2 - x)) * hG -
      ((x2 - x) ^ 2) * hx2 + (2 * (x2 - x)) * hs
  have hid : (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) ^ 2 - (6 * x ^ 2 + 4 * W.a₂ * x + 2 * W.a₄ + W.a₁ ^ 2 * x + W.a₁ * W.a₃) * (3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 + 3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 + 3 * (W.a₃ ^ 2 + 4 * W.a₆) * x + (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2)) + (2 * x ^ 6 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 5 + 5 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 4 + 10 * (W.a₃ ^ 2 + 4 * W.a₆) * x ^ 3 + 10 * (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2) * x ^ 2 + ((W.a₁ ^ 2 + 4 * W.a₂) * (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2) - (W.a₁ * W.a₃ + 2 * W.a₄) * (W.a₃ ^ 2 + 4 * W.a₆)) * x + ((W.a₁ * W.a₃ + 2 * W.a₄) * (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2) - (W.a₃ ^ 2 + 4 * W.a₆) ^ 2)) = 0 := by
    ring
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) ^ 2 * hH + (((x3 - x) * ((3 * x ^ 4 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 3 + 3 * (W.a₁ * W.a₃ + 2 * W.a₄) * x ^ 2 + 3 * (W.a₃ ^ 2 + 4 * W.a₆) * x + (W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2)) - (x2 - x) * (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆))) + (6 * x ^ 2 + 4 * W.a₂ * x + 2 * W.a₄ + W.a₁ ^ 2 * x + W.a₁ * W.a₃) * (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆))) * hwF) +
    (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) ^ 2 * hu + (4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (W.a₁ * W.a₃ + 2 * W.a₄) * x + (W.a₃ ^ 2 + 4 * W.a₆)) * hid

end MPP.Solutions.Bsd264
