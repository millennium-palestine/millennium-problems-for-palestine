import Mathlib

namespace MPP.Solutions.Bsd127

theorem main : ∀ (p q e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e1 + e2 + e3 = 0 → p = e1 * e2 + e1 * e3 + e2 * e3 → q = -(e1 * e2 * e3) →
    e1 ≠ e2 ∧ e1 ≠ e3 ∧ e2 ≠ e3 := by
  intro p q e1 e2 e3 E _ ha1 ha2 ha3 ha4 ha6 hs hp hq
  have hΔu : E.Δ ≠ 0 := WeierstrassCurve.IsElliptic.isUnit.ne_zero
  have hΔ : E.Δ = -16 * (4 * p ^ 3 + 27 * q ^ 2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha1, ha2, ha3, ha4, ha6]
    ring
  have hPi : ((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 = -(4 * p ^ 3 + 27 * q ^ 2) := by
    have he3 : e3 = -e1 - e2 := by linarith
    subst he3
    subst hp
    subst hq
    ring
  have hne : (e1 - e2) * (e1 - e3) * (e2 - e3) ≠ 0 := by
    intro h0
    apply hΔu
    have h4 : 4 * p ^ 3 + 27 * q ^ 2 = -(((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2) := by
      linarith [hPi]
    rw [hΔ, h4, h0]
    ring
  refine ⟨fun h => hne ?_, fun h => hne ?_, fun h => hne ?_⟩
  · rw [h]
    ring
  · rw [h]
    ring
  · rw [h]
    ring

end MPP.Solutions.Bsd127
