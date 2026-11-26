import Mathlib
import MPP.Solutions.Bsd264
import MPP.Solutions.Bsd307

namespace MPP.Solutions.Bsd308

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (x y : K)
    (h : W.toAffine.Nonsingular x y), (2 : K) = 0 →
    2 * y + W.a₁ * x + W.a₃ ≠ 0 →
    (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ ≠ 0 := by
  intro K _ _ W _ x y h h2 hD h5
  intro hΨ
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h with hPdef
  -- 2P is not zero: otherwise P = -P, which forces 2y + a₁x + a₃ = 0
  have hP2 : (2 : ℤ) • P ≠ 0 := by
    intro h20
    have hPP : P + P = 0 := by rw [← two_zsmul]; exact h20
    have hneg : P = -P := add_eq_zero_iff_eq_neg.mp hPP
    rw [hPdef, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq] at hneg
    obtain ⟨_, hy⟩ := hneg
    apply hD
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  -- the case 3P = 0 gives 2P = 5P - 3P = 0
  by_cases h30 : (3 : ℤ) • P = 0
  · apply hP2
    have e : (2 : ℤ) • P + (3 : ℤ) • P = 0 := by
      rw [← add_zsmul]
      norm_num
      exact h5
    rw [h30, add_zero] at e
    exact e
  -- otherwise 3P = (x3, y3) is affine
  obtain ⟨x3, y3, h3, hx3⟩ : ∃ (x3 y3 : K) (h3 : W.toAffine.Nonsingular x3 y3),
      (3 : ℤ) • P = WeierstrassCurve.Affine.Point.some x3 y3 h3 := by
    rcases hm : (3 : ℤ) • P with _ | ⟨x3, y3, h3⟩
    · exact absurd hm h30
    · exact ⟨x3, y3, h3, rfl⟩
  -- bsd-264: x3 Ψ₃² = x Ψ₃² − Ψ₂Sq preΨ₄, and Ψ₃ = 0 leaves Ψ₂Sq preΨ₄ = 0
  have hk := MPP.Solutions.Bsd264.main K W x y x3 y3 h h3 hD hx3
  rw [hΨ] at hk
  have hprod : (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) *
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
        (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) = 0 := by
    linear_combination hk
  -- the curve equation gives Ψ₂Sq(x) = (2y + a₁x + a₃)² ≠ 0
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hE
  have hsq0 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 := by
    rw [← hsq]
    exact pow_ne_zero 2 hD
  have hpre := (mul_eq_zero.mp hprod).resolve_left hsq0
  -- bsd-307: a common root of Ψ₃ and preΨ₄ in characteristic 2 forces the discriminant to vanish
  have hΔ := MPP.Solutions.Bsd307.main K W x h2 hΨ hpre
  exact W.isUnit_Δ.ne_zero hΔ

end MPP.Solutions.Bsd308
