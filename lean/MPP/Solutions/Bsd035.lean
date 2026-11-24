import Mathlib
import MPP.Solutions.Bsd030

namespace MPP.Solutions.Bsd035

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (M : ℕ),
    {P : E.toAffine.Point | P = 0 ∨ ∃ x y : ℚ, ∃ h : E.toAffine.Nonsingular x y,
      P = WeierstrassCurve.Affine.Point.some x y h ∧ x.num.natAbs ≤ M ∧ x.den ≤ M}.Finite := by
  intro E _ M
  classical
  let g : ℚ × ℚ → E.toAffine.Point := fun p =>
    if h : E.toAffine.Nonsingular p.1 p.2 then WeierstrassCurve.Affine.Point.some p.1 p.2 h else 0
  have hT := MPP.Solutions.Bsd030.main E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ M
  refine ((Set.finite_singleton (0 : E.toAffine.Point)).union (hT.image g)).subset ?_
  rintro P (rfl | ⟨x, y, h, rfl, hn, hd⟩)
  · exact Or.inl (Set.mem_singleton _)
  · refine Or.inr ⟨(x, y), ?_, ?_⟩
    · show y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ ∧
        x.num.natAbs ≤ M ∧ x.den ≤ M
      exact ⟨(WeierstrassCurve.Affine.equation_iff x y).mp h.1, hn, hd⟩
    · show (if h' : E.toAffine.Nonsingular x y then
          WeierstrassCurve.Affine.Point.some x y h' else 0) = _
      rw [dif_pos h]

end MPP.Solutions.Bsd035
