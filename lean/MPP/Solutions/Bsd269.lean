import Mathlib

namespace MPP.Solutions.Bsd269

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (x y : K),
    W.toAffine.Nonsingular x y →
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  intro K _ W x y h
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * hE

end MPP.Solutions.Bsd269
