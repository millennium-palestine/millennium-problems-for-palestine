import Mathlib
import MPP.Solutions.Bsd413

namespace MPP.Solutions.Bsd414

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) [W.IsElliptic],
    (3 : K) ≠ 0 → Squarefree (W.preΨ' 3) := by
  intro K _ W _ h3
  rw [WeierstrassCurve.preΨ'_three]
  obtain ⟨u, v, h⟩ := MPP.Solutions.Bsd413.main K W.b₂ W.b₄ W.b₆ W.b₈ W.b_relation
  have hd : Polynomial.derivative W.Ψ₃ =
      12 * Polynomial.X ^ 3 + 3 * Polynomial.C W.b₂ * Polynomial.X ^ 2 +
        6 * Polynomial.C W.b₄ * Polynomial.X + 3 * Polynomial.C W.b₆ := by
    simp [WeierstrassCurve.Ψ₃, map_ofNat]
    ring
  have hΔ : W.Δ = -W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 := by
    simp only [WeierstrassCurve.Δ]
    ring
  have hunit : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hc : (-81 * W.Δ ^ 2 : K) ≠ 0 := by
    have h81 : (81 : K) ≠ 0 := by
      have : (81 : K) = 3 ^ 4 := by norm_num
      rw [this]
      exact pow_ne_zero 4 h3
    exact mul_ne_zero (neg_ne_zero.mpr h81) (pow_ne_zero 2 hunit)
  have key : u * W.Ψ₃ + v * Polynomial.derivative W.Ψ₃ = Polynomial.C (-81 * W.Δ ^ 2) := by
    rw [hd, hΔ]
    exact h
  apply Polynomial.Separable.squarefree
  refine ⟨Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * u, Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * v, ?_⟩
  calc Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * u * W.Ψ₃ +
        Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * v * Polynomial.derivative W.Ψ₃
      = Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * (u * W.Ψ₃ + v * Polynomial.derivative W.Ψ₃) := by ring
    _ = Polynomial.C (-81 * W.Δ ^ 2)⁻¹ * Polynomial.C (-81 * W.Δ ^ 2) := by rw [key]
    _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]

end MPP.Solutions.Bsd414
