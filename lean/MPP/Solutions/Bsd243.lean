import Mathlib

namespace MPP.Solutions.Bsd243

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] (x : K),
    (2 : K) ≠ 0 → ∃ y : K, W.toAffine.Nonsingular x y := by
  intro K _ _ W _ x h2
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    ((W.a₁ * x + W.a₃) ^ 2 + 4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) (by norm_num : 0 < 2)
  obtain ⟨y, hy⟩ : ∃ y : K, 2 * y = -(W.a₁ * x + W.a₃) + s :=
    ⟨(-(W.a₁ * x + W.a₃) + s) / 2, by field_simp⟩
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have key : 4 * (y ^ 2 + (W.a₁ * x + W.a₃) * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) = 0 := by
    linear_combination (2 * y + (W.a₁ * x + W.a₃) + s) * hy + hs
  have hR : y ^ 2 + (W.a₁ * x + W.a₃) * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 :=
    (mul_eq_zero.mp key).resolve_left h4
  have heq : W.toAffine.Equation x y :=
    (WeierstrassCurve.Affine.equation_iff (W := W) x y).mpr (by linear_combination hR)
  exact ⟨y, WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq⟩

end MPP.Solutions.Bsd243
