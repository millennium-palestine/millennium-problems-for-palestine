import Mathlib

namespace MPP.Solutions.Bsd206

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    (x : K), ∃ y : K, W.toAffine.Nonsingular x y := by
  intro K _ _ W _ x
  let P : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X
    - Polynomial.C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hdeg : P.degree ≠ 0 := by
    have h2 : P.degree = 2 := by
      dsimp only [P]
      compute_degree!
    rw [h2]
    decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root P hdeg
  refine ⟨y, (WeierstrassCurve.Affine.equation_iff_nonsingular).mp ?_⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hy
  linear_combination hy

end MPP.Solutions.Bsd206
