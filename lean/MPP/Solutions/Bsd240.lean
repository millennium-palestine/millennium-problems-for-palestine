import Mathlib

namespace MPP.Solutions.Bsd240

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0 →
    (3 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 := by
  intro K _ _ W x y h hD hΨ
  have hy' : ¬ (y = -y - W.a₁ * x - W.a₃) := fun h' => hD (by linear_combination h')
  have hy : y ≠ W.toAffine.negY x y := fun h' => hy' (by simpa [WeierstrassCurve.Affine.negY] using h')
  have hc := (WeierstrassCurve.Affine.equation_iff' x y).mp h.1
  -- the double of P, as in bsd-205
  have hdbl := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hy
  -- the x-coordinate of 2P is x, since Ψ₃(x) = 0 (bsd-205 with the division removed)
  have hx3 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hD2 : (2 * y + W.a₁ * x + W.a₃) ^ 2 ≠ 0 := pow_ne_zero 2 hD
    apply mul_right_cancel₀ hD2
    rw [WeierstrassCurve.Affine.slope_of_Y_ne' hy']
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hΨ ⊢
    have hD' : y - (-y - W.a₁ * x - W.a₃) ≠ 0 := fun h0 => hD (by linear_combination h0)
    have hℓ := div_mul_cancel₀ (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) hD'
    generalize (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (y - (-y - W.a₁ * x - W.a₃)) = ℓ at hℓ ⊢
    linear_combination (ℓ * (y - (-y - W.a₁ * x - W.a₃)) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
      + W.a₁ * (y - (-y - W.a₁ * x - W.a₃))) * hℓ + (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x)) * hc - hΨ
  -- two affine points with the same x-coordinate are equal or opposite (bsd-217)
  have same : ∀ (x' y' : K) (h' : W.toAffine.Nonsingular x' y'), x' = x →
      (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
          WeierstrassCurve.Affine.Point.some x' y' h' ∨
        (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
          -(WeierstrassCurve.Affine.Point.some x' y' h' : W.toAffine.Point) := by
    intro x' y' h' hx'
    have e₁ := (WeierstrassCurve.Affine.equation_iff (W := W) x y).mp h.1
    have e₂ := (WeierstrassCurve.Affine.equation_iff (W := W) x' y').mp h'.1
    rw [hx'] at e₂
    have hfac : (y - y') * (y + y' + W.a₁ * x + W.a₃) = 0 := by
      linear_combination e₁ - e₂
    rcases mul_eq_zero.mp hfac with h0 | h0
    · left
      have hyy : y = y' := sub_eq_zero.mp h0
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx'.symm, hyy⟩
    · right
      rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx'.symm, by rw [WeierstrassCurve.Affine.negY, hx']; linear_combination h0⟩
  rcases same _ _ (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.2)) hx3 with hA | hB
  · -- 2P = P would force P = 0, impossible for an affine point
    rw [← hA] at hdbl
    simp at hdbl
  · -- 2P = −P, so 3P = P + (P + P) = P + (−P) = 0
    have hPP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = -(WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
      rw [hdbl, hB, neg_neg]
    rw [show (3 : ℤ) = 1 + 2 by norm_num, add_zsmul, one_zsmul, two_zsmul, hPP]
    exact add_neg_cancel _

end MPP.Solutions.Bsd240
