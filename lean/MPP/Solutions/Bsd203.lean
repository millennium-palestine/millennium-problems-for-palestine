import Mathlib

namespace MPP.Solutions.Bsd203

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (x y : K),
    y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ →
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) ^ 2 +
        W.a₁ * ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) -
        W.a₂ - 2 * x = x →
      (W.preΨ' 3).eval x = 0 := by
  intro K _ W x y hE hD hlam
  have hND : ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃)) *
      (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y :=
    div_mul_cancel₀ _ hD
  generalize (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) / (2 * y + W.a₁ * x + W.a₃) = l at hlam hND
  have hF : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2 +
      W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) -
      (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2 = 0 := by
    linear_combination (2 * y + W.a₁ * x + W.a₃) ^ 2 * hlam -
      ((3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) + l * (2 * y + W.a₁ * x + W.a₃) +
        W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hND
  rw [WeierstrassCurve.preΨ'_three]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat]
  linear_combination (-1 : K) * hF - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hE

end MPP.Solutions.Bsd203
