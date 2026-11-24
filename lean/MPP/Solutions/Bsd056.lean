import Mathlib
import MPP.Solutions.Bsd053
import MPP.Solutions.Bsd055

namespace MPP.Solutions.Bsd056

theorem main : ∀ (e1 e2 e3 : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic], e1 + e2 + e3 = 0 → e1 ≠ e2 → e1 ≠ e3 →
    e2 ≠ e3 → E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = e1 * e2 + e1 * e3 + e2 * e3 → E.a₆ = -(e1 * e2 * e3) →
    ∀ (x y : ℚ) (h : E.toAffine.Nonsingular x y), y ≠ 0 →
      (∃ a1 a2 a3 : ℚ, a1 ^ 2 + e1 = x ∧ a2 ^ 2 + e2 = x ∧ a3 ^ 2 + e3 = x) →
        ∃ R : E.toAffine.Point, R + R = WeierstrassCurve.Affine.Point.some _ _ h := by
  intro e1 e2 e3 E _ hs h12 h13 h23 ha1 ha2 ha3 ha4 ha6 x y h hy hA
  obtain ⟨a1, a2, a3, hA1, hA2, hA3⟩ := hA
  have hn12 : a1 + a2 ≠ 0 := by
    intro h0
    have h2 : a2 = -a1 := by linarith
    apply h12
    have : a2 ^ 2 = a1 ^ 2 := by rw [h2]; ring
    linarith
  have hn13 : a1 + a3 ≠ 0 := by
    intro h0
    have h2 : a3 = -a1 := by linarith
    apply h13
    have : a3 ^ 2 = a1 ^ 2 := by rw [h2]; ring
    linarith
  have hn23 : a2 + a3 ≠ 0 := by
    intro h0
    have h2 : a3 = -a2 := by linarith
    apply h23
    have : a3 ^ 2 = a2 ^ 2 := by rw [h2]; ring
    linarith
  obtain ⟨xR, hxR⟩ : ∃ t : ℚ, t = x + a1 * a2 + a2 * a3 + a3 * a1 := ⟨_, rfl⟩
  obtain ⟨yR, hyR⟩ : ∃ t : ℚ, t = (a1 + a2) * (a1 + a3) * (a2 + a3) := ⟨_, rfl⟩
  have hyR0 : yR ≠ 0 := by
    rw [hyR]
    exact mul_ne_zero (mul_ne_zero hn12 hn13) hn23
  -- the curve equation at (xR, yR): the square of yR is the cubic at xR
  have key : yR ^ 2 = xR ^ 3 + (e1 * e2 + e1 * e3 + e2 * e3) * xR + -(e1 * e2 * e3) := by
    have he1 : e1 = x - a1 ^ 2 := by linarith
    have he2 : e2 = x - a2 ^ 2 := by linarith
    have he3 : e3 = x - a3 ^ 2 := by linarith
    have hx : x = (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) / 3 := by
      rw [he1, he2, he3] at hs
      linarith
    rw [hxR, hyR, he1, he2, he3, hx]
    ring
  have hcurve : E.toAffine.Equation xR yR := by
    rw [WeierstrassCurve.Affine.equation_iff]
    show yR ^ 2 + E.a₁ * xR * yR + E.a₃ * yR = xR ^ 3 + E.a₂ * xR ^ 2 + E.a₄ * xR + E.a₆
    rw [ha1, ha2, ha3, ha4, ha6]
    linear_combination key
  have hR : E.toAffine.Nonsingular xR yR := WeierstrassCurve.Affine.equation_iff_nonsingular.mp hcurve
  -- the doubling formula and the halving identity
  obtain ⟨x', y', h', hsum, hx'⟩ :=
    Bsd055.main (e1 * e2 + e1 * e3 + e2 * e3) (-(e1 * e2 * e3)) E ha1 ha2 ha3 ha4 ha6 xR yR hR hyR0
  have hal := Bsd053.main e1 e2 e3 a1 a2 a3 hs (by linarith) (by linarith)
  rw [hA1] at hal
  rw [← hxR] at hal
  have hq : ((3 * xR ^ 2 + (e1 * e2 + e1 * e3 + e2 * e3)) / (2 * yR)) ^ 2 = x + 2 * xR := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (mul_ne_zero two_ne_zero hyR0))]
    linear_combination hal - 4 * (x + 2 * xR) * key
  have hx2 : x' = x := by
    rw [hx', hq]
    ring
  have hy2 : y' = y ∨ y' = E.toAffine.negY x y :=
    WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 h.1 hx2
  rcases hy2 with hy2 | hy2
  · refine ⟨WeierstrassCurve.Affine.Point.some _ _ hR, ?_⟩
    rw [hsum]
    subst hx2 hy2
    rfl
  · refine ⟨-WeierstrassCurve.Affine.Point.some _ _ hR, ?_⟩
    rw [← neg_add_rev, hsum, WeierstrassCurve.Affine.Point.neg_some]
    subst hx2 hy2
    congr 1
    simp [WeierstrassCurve.Affine.negY]
    ring

end MPP.Solutions.Bsd056
