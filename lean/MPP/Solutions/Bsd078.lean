import Mathlib
import MPP.Solutions.Bsd068
import MPP.Solutions.Bsd077

namespace MPP.Solutions.Bsd078

theorem main : ∀ (p q : ℚ) (K : Type) [Field K] [Algebra ℚ K] (t : K) (E : WeierstrassCurve ℚ),
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    t ^ 3 + algebraMap ℚ K p * t + algebraMap ℚ K q = 0 →
    ∀ (x1 y1 x2 y2 x3 y3 : ℚ) (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2)
      (h3 : E.toAffine.Nonsingular x3 y3),
      WeierstrassCurve.Affine.Point.some _ _ h1 + WeierstrassCurve.Affine.Point.some _ _ h2 =
          WeierstrassCurve.Affine.Point.some _ _ h3 →
      algebraMap ℚ K x1 ≠ t → algebraMap ℚ K x2 ≠ t →
      ∃ r : K, (algebraMap ℚ K x3 - t) * (algebraMap ℚ K x1 - t) * (algebraMap ℚ K x2 - t) = r ^ 2 := by
  intro p q K _ _ t E ha1 ha2 ha3 ha4 ha6 ht x1 y1 x2 y2 x3 y3 h1 h2 h3 hsum hne1 hne2
  by_cases hx : x1 = x2
  · subst hx
    have hnz : y1 ≠ E.toAffine.negY x1 y2 := by
      intro hy
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hy] at hsum
      exact WeierstrassCurve.Affine.Point.some_ne_zero h3 hsum.symm
    have hyy : y1 = y2 := by
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
      · exact h
      · exact absurd h hnz
    subst hyy
    have hy0 : y1 ≠ 0 := by
      intro h0
      apply hnz
      simp [WeierstrassCurve.Affine.negY, ha1, ha3, h0]
    obtain ⟨x4, y4, h4, hs4, r, hr⟩ :=
      MPP.Solutions.Bsd077.main p q K t E ha1 ha2 ha3 ha4 ha6 ht x1 y1 h1 hy0 hne1
    have hx34 : x4 = x3 := by
      have := hs4.symm.trans hsum
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.1
    subst hx34
    exact ⟨(algebraMap ℚ K x1 - t) * r, by rw [hr]; ring⟩
  · obtain ⟨x4, y4, h4, hs4, r, hr⟩ :=
      MPP.Solutions.Bsd068.main p q K t E ha1 ha2 ha3 ha4 ha6 ht x1 y1 x2 y2 h1 h2 hx hne1 hne2
    have hx34 : x4 = x3 := by
      have := hs4.symm.trans hsum
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at this
      exact this.1
    subst hx34
    exact ⟨(algebraMap ℚ K x1 - t) * (algebraMap ℚ K x2 - t) * r, by rw [hr]; ring⟩

end MPP.Solutions.Bsd078
