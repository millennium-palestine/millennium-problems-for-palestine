import Mathlib

namespace MPP.Solutions.Bsd055

theorem main : ∀ (p q : ℚ) (E : WeierstrassCurve ℚ), E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y), y ≠ 0 →
      ∃ (x' y' : ℚ) (h' : E.toAffine.Nonsingular x' y'),
        WeierstrassCurve.Affine.Point.some _ _ h + WeierstrassCurve.Affine.Point.some _ _ h =
          WeierstrassCurve.Affine.Point.some _ _ h' ∧
        x' = ((3 * x ^ 2 + p) / (2 * y)) ^ 2 - 2 * x := by
  intro p q E ha1 ha2 ha3 ha4 ha6 x y h hy
  have hneg : E.toAffine.negY x y = -y := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3]
  have hyne : y ≠ E.toAffine.negY x y := by
    rw [hneg]
    intro h'
    apply hy
    linarith
  refine ⟨E.toAffine.addX x x (E.toAffine.slope x x y y), E.toAffine.addY x x y (E.toAffine.slope x x y y),
    WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hyne hxy.right), ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne]
  · have hs : E.toAffine.slope x x y y = (3 * x ^ 2 + p) / (2 * y) := by
      unfold WeierstrassCurve.Affine.slope
      rw [if_pos rfl, if_neg (by rw [hneg]; intro h'; apply hy; linarith)]
      rw [hneg, ha2, ha1, ha4, show y - -y = 2 * y by ring]
      ring
    rw [hs]
    simp [WeierstrassCurve.Affine.addX, ha1, ha2]
    ring

end MPP.Solutions.Bsd055
