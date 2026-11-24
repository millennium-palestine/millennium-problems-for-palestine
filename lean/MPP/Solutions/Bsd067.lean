import Mathlib

namespace MPP.Solutions.Bsd067

theorem main : ∀ (p q : ℚ) (K : Type) [Field K] [Algebra ℚ K] (t : K),
    t ^ 3 + algebraMap ℚ K p * t + algebraMap ℚ K q = 0 →
    ∀ (x1 y1 x2 y2 lam x3 : ℚ), y1 ^ 2 = x1 ^ 3 + p * x1 + q → y2 ^ 2 = x2 ^ 3 + p * x2 + q →
      x1 ≠ x2 → algebraMap ℚ K x1 ≠ t → algebraMap ℚ K x2 ≠ t → lam * (x1 - x2) = y1 - y2 →
      x3 = lam ^ 2 - x1 - x2 →
      ∃ r : K, algebraMap ℚ K x3 - t = (algebraMap ℚ K x1 - t) * (algebraMap ℚ K x2 - t) * r ^ 2 := by
  intro p q K _ _ t ht x1 y1 x2 y2 lam x3 h1 h2 hne h1t h2t hl hx3
  have sq : ∀ (a b c s : K), a ≠ 0 → b ≠ 0 → a * b * c = s ^ 2 → ∃ r : K, c = a * b * r ^ 2 := by
    intro a b c s ha hb h
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    refine ⟨s / (a * b), ?_⟩
    have h2' : a * b * (s / (a * b)) ^ 2 = s ^ 2 / (a * b) := by
      rw [div_pow]
      field_simp
    rw [h2', eq_div_iff hab]
    linear_combination h
  have hsub : x1 - x2 ≠ 0 := sub_ne_zero.mpr hne
  have hA : (x1 - x2) * (lam * (y1 + y2) - (x1 ^ 2 + x1 * x2 + x2 ^ 2 + p)) = 0 := by
    linear_combination (y1 + y2) * hl + h1 - h2
  have hA' : lam * (y1 + y2) = x1 ^ 2 + x1 * x2 + x2 ^ 2 + p := by
    have h0 := (mul_eq_zero.mp hA).resolve_left hsub
    linarith
  have hy1 : 2 * lam * y1 = (x1 ^ 2 + x1 * x2 + x2 ^ 2 + p) + lam ^ 2 * (x1 - x2) := by
    linear_combination hA' - lam * hl
  have K1 := congrArg (algebraMap ℚ K) h1
  have Ky := congrArg (algebraMap ℚ K) hy1
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at K1 Ky
  have hid : (algebraMap ℚ K x1 - t) * (algebraMap ℚ K x2 - t) * (algebraMap ℚ K x3 - t) =
      (algebraMap ℚ K y1 - algebraMap ℚ K lam * (algebraMap ℚ K x1 - t)) ^ 2 := by
    rw [hx3]
    simp only [map_sub, map_pow]
    linear_combination (-1 : K) * K1 + (algebraMap ℚ K x1 - t) * Ky - ht
  obtain ⟨r, hr⟩ := sq (algebraMap ℚ K x1 - t) (algebraMap ℚ K x2 - t) (algebraMap ℚ K x3 - t)
    (algebraMap ℚ K y1 - algebraMap ℚ K lam * (algebraMap ℚ K x1 - t))
    (sub_ne_zero.mpr h1t) (sub_ne_zero.mpr h2t) hid
  exact ⟨r, hr⟩

end MPP.Solutions.Bsd067
