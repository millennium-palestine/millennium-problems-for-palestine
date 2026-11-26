import Mathlib
import MPP.Solutions.Bsd276
import MPP.Solutions.Bsd283

namespace MPP.Solutions.Bsd310

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic] (x y : K),
    W.toAffine.Nonsingular x y → (2 : K) ≠ 0 → (3 : K) ≠ 0 → (5 : K) ≠ 0 →
    (W.preΨ' 5).eval x = 0 → 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
  intro K _ _ W _ x y h h2 h3 h5 hroot hz
  -- the curve equation gives Ψ₂Sq(x) = (2y + a₁x + a₃)² = 0
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx' := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx'
    exact hx'
  have hsq2 : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    have e : (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination 4 * hE
    rw [← e, hz]
    ring
  -- ψ₅ = preΨ₄·Ψ₂Sq² − Ψ₃³ (bsd-283), so ψ₅(x) = 0 with Ψ₂Sq(x) = 0 forces Ψ₃(x) = 0
  have hev : (W.preΨ' 5).eval x =
      (2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 + 10 * W.b₈ * x ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2)) *
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 -
        (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 := by
    rw [MPP.Solutions.Bsd283.main K W]
    simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃]
  have hroot' := hroot
  rw [hev, hsq2] at hroot'
  have h3' : (3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈) ^ 3 = 0 := by
    linear_combination -hroot'
  exact MPP.Solutions.Bsd276.main K W x h2 h3 h5
    (pow_eq_zero_iff (by norm_num) |>.mp h3') hroot

end MPP.Solutions.Bsd310
