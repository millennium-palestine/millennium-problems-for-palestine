import Mathlib

namespace MPP.Solutions.Bsd065

theorem main : ∀ (p q e : ℚ) (E : WeierstrassCurve ℚ), E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    e ^ 3 + p * e + q = 0 →
    ∀ (x1 y1 x2 y2 : ℚ) (h1 : E.toAffine.Nonsingular x1 y1) (h2 : E.toAffine.Nonsingular x2 y2),
      x1 ≠ x2 → x1 ≠ e → x2 ≠ e →
      ∃ (x3 y3 : ℚ) (h3 : E.toAffine.Nonsingular x3 y3),
        WeierstrassCurve.Affine.Point.some _ _ h1 + WeierstrassCurve.Affine.Point.some _ _ h2 =
          WeierstrassCurve.Affine.Point.some _ _ h3 ∧
        ∃ r : ℚ, x3 - e = (x1 - e) * (x2 - e) * r ^ 2 := by
  intro p q e E ha1 ha2 ha3 ha4 ha6 he
  have sq : ∀ (a b c s : ℚ), a ≠ 0 → b ≠ 0 → a * b * c = s ^ 2 → ∃ r : ℚ, c = a * b * r ^ 2 := by
    intro a b c s ha hb h
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    refine ⟨s / (a * b), ?_⟩
    have h2' : a * b * (s / (a * b)) ^ 2 = s ^ 2 / (a * b) := by
      rw [div_pow]
      field_simp
    rw [h2', eq_div_iff hab]
    linear_combination h
  have key : ∀ (x1 y1 x2 y2 lam x3 : ℚ), y1 ^ 2 = x1 ^ 3 + p * x1 + q → y2 ^ 2 = x2 ^ 3 + p * x2 + q →
      x1 ≠ x2 → x1 ≠ e → x2 ≠ e → lam * (x1 - x2) = y1 - y2 → x3 = lam ^ 2 - x1 - x2 →
      ∃ r : ℚ, x3 - e = (x1 - e) * (x2 - e) * r ^ 2 := by
    intro x1 y1 x2 y2 lam x3 h1 h2 hne h1e h2e hl hx3
    have hsub : x1 - x2 ≠ 0 := sub_ne_zero.mpr hne
    have hA : (x1 - x2) * (lam * (y1 + y2) - (x1 ^ 2 + x1 * x2 + x2 ^ 2 + p)) = 0 := by
      linear_combination (y1 + y2) * hl + h1 - h2
    have hA' : lam * (y1 + y2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + p := by
      have h0 := (mul_eq_zero.mp hA).resolve_left hsub
      linarith
    have hy1 : 2 * lam * y1 = (x1 ^ 2 + x1 * x2 + x2 ^ 2 + p) + lam ^ 2 * (x1 - x2) := by
      linear_combination hA' - lam * hl
    have hid : (x1 - e) * (x2 - e) * (x3 - e) = (y1 - lam * (x1 - e)) ^ 2 := by
      rw [hx3]
      linear_combination (-1 : ℚ) * h1 + (x1 - e) * hy1 - he
    obtain ⟨r, hr⟩ := sq (x1 - e) (x2 - e) (x3 - e) (y1 - lam * (x1 - e))
      (sub_ne_zero.mpr h1e) (sub_ne_zero.mpr h2e) hid
    exact ⟨r, hr⟩
  intro x1 y1 x2 y2 h1 h2 hne h1e h2e
  have hc1 : y1 ^ 2 = x1 ^ 3 + p * x1 + q := by
    have h := (WeierstrassCurve.Affine.equation_iff x1 y1).mp h1.1
    rw [ha1, ha2, ha3, ha4, ha6] at h
    linear_combination h
  have hc2 : y2 ^ 2 = x2 ^ 3 + p * x2 + q := by
    have h := (WeierstrassCurve.Affine.equation_iff x2 y2).mp h2.1
    rw [ha1, ha2, ha3, ha4, ha6] at h
    linear_combination h
  have hsub : x1 - x2 ≠ 0 := sub_ne_zero.mpr hne
  have hl : (y1 - y2) / (x1 - x2) * (x1 - x2) = y1 - y2 := div_mul_cancel₀ _ hsub
  obtain ⟨r, hr⟩ := key x1 y1 x2 y2 ((y1 - y2) / (x1 - x2)) (((y1 - y2) / (x1 - x2)) ^ 2 - x1 - x2)
    hc1 hc2 hne h1e h2e hl rfl
  refine ⟨_, _, _, WeierstrassCurve.Affine.Point.add_of_X_ne hne, ?_⟩
  refine ⟨r, ?_⟩
  rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
  simp only [WeierstrassCurve.Affine.addX, ha1, ha2, zero_mul, sub_zero, add_zero]
  linear_combination hr

end MPP.Solutions.Bsd065
