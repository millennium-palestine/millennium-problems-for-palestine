import Mathlib

namespace MPP.Solutions.Bsd077

theorem main : ∀ (p q : ℚ) (K : Type) [Field K] [Algebra ℚ K] (t : K) (E : WeierstrassCurve ℚ),
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    t ^ 3 + algebraMap ℚ K p * t + algebraMap ℚ K q = 0 →
    ∀ (x1 y1 : ℚ) (h1 : E.toAffine.Nonsingular x1 y1), y1 ≠ 0 → algebraMap ℚ K x1 ≠ t →
      ∃ (x3 y3 : ℚ) (h3 : E.toAffine.Nonsingular x3 y3),
        WeierstrassCurve.Affine.Point.some _ _ h1 + WeierstrassCurve.Affine.Point.some _ _ h1 =
          WeierstrassCurve.Affine.Point.some _ _ h3 ∧
        ∃ r : K, algebraMap ℚ K x3 - t = r ^ 2 := by
  intro p q K _ _ t E ha1 ha2 ha3 ha4 ha6 ht x1 y1 h1 hy hne
  have hc1 : y1 ^ 2 = x1 ^ 3 + p * x1 + q := by
    have h := (WeierstrassCurve.Affine.equation_iff x1 y1).mp h1.1
    rw [ha1, ha2, ha3, ha4, ha6] at h
    linear_combination h
  have hn : E.toAffine.negY x1 y1 = -y1 := by
    simp [WeierstrassCurve.Affine.negY, ha1, ha3]
  have hyneg : y1 ≠ E.toAffine.negY x1 y1 := by
    rw [hn]
    intro h
    apply hy
    linarith
  have hsl : E.toAffine.slope x1 x1 y1 y1 * (2 * y1) = 3 * x1 ^ 2 + p := by
    have hyv : 2 * y1 ≠ 0 := by
      intro h
      apply hy
      linarith
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg, hn]
    simp only [ha1, ha2, ha4]
    field_simp
    ring
  have K74 : ∀ (lam x3 : ℚ), lam * (2 * y1) = 3 * x1 ^ 2 + p → x3 = lam ^ 2 - 2 * x1 →
      ∃ r : K, algebraMap ℚ K x3 - t = r ^ 2 := by
    intro lam x3 hl hx3
    have hcurve := congrArg (algebraMap ℚ K) hc1
    have hslope := congrArg (algebraMap ℚ K) hl
    have hx3K := congrArg (algebraMap ℚ K) hx3
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at hcurve hslope hx3K
    have hxt : algebraMap ℚ K x1 - t ≠ 0 := sub_ne_zero.mpr hne
    have hid : (algebraMap ℚ K x1 - t) ^ 2 * (algebraMap ℚ K x3 - t) =
        (algebraMap ℚ K y1 - algebraMap ℚ K lam * (algebraMap ℚ K x1 - t)) ^ 2 := by
      rw [hx3K]
      linear_combination (-1 : K) * hcurve + (algebraMap ℚ K x1 - t) * hslope - ht
    refine ⟨(algebraMap ℚ K y1 - algebraMap ℚ K lam * (algebraMap ℚ K x1 - t)) /
      (algebraMap ℚ K x1 - t), ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hxt)]
    linear_combination hid
  refine ⟨_, _, _, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg, ?_⟩
  obtain ⟨r, hr⟩ := K74 (E.toAffine.slope x1 x1 y1 y1)
    (E.toAffine.addX x1 x1 (E.toAffine.slope x1 x1 y1 y1)) hsl (by
      simp only [WeierstrassCurve.Affine.addX, ha1, ha2]
      ring)
  exact ⟨r, hr⟩

end MPP.Solutions.Bsd077
