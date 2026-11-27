import Mathlib
import MPP.Solutions.Bsd271

namespace MPP.Solutions.Bsd394

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y x₃ y₃ : K)
    (h : W.toAffine.Nonsingular x y) (h₃ : W.toAffine.Nonsingular x₃ y₃),
    (3 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ →
    x₃ * (W.Ψ₃.eval x) ^ 2 = x * (W.Ψ₃.eval x) ^ 2 - W.Ψ₂Sq.eval x * W.preΨ₄.eval x := by
  intro K _ _ W x y x₃ y₃ h h₃ h3P
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hD' : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    rw [WeierstrassCurve.Affine.negY]
    ring
  have hΨ : W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination (-4) * hE
  have hP3 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
      ((WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ := by
    rw [← h3P, three_nsmul]
  by_cases hyne : y = W.toAffine.negY x y
  · -- 2 • P = 0, so 3 • P = P and x₃ = x; the right side has Ψ₂Sq(x) = 0
    have h2 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyne
    have hP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₃ y₃ h₃ := by
      rw [← hP3, h2, add_zero]
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
    have hz : 2 * y + W.a₁ * x + W.a₃ = 0 := by
      have hD := hD'
      rw [← hyne, sub_self] at hD
      exact hD.symm
    rw [← hP.1, hΨ, hz]
    ring
  · -- 2 • P ≠ 0: the chord P + 2P is the triple, which is the bsd-271 identity
    have key := MPP.Solutions.Bsd271.main K W x y x₃ y₃ h h₃ hyne hP3
    norm_num [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq]
    linear_combination key

end MPP.Solutions.Bsd394
