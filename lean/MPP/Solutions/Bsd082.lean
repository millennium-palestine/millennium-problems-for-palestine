import Mathlib

namespace MPP.Solutions.Bsd082

theorem main : ∀ (p q x y : ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic],
    E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 → E.a₄ = p → E.a₆ = q →
    ∀ (h : E.toAffine.Nonsingular x y), y ≠ 0 →
      (∃ u v w : ℚ, u ^ 2 - 2 * q * v * w = x ∧ 2 * u * v - 2 * p * v * w - q * w ^ 2 = -1 ∧
        v ^ 2 + 2 * u * w - p * w ^ 2 = 0) →
      ∃ R : E.toAffine.Point, R + R = WeierstrassCurve.Affine.Point.some _ _ h := by
  -- the identity of bsd-081, proved inside
  have key : ∀ (p q x u v w xR yR : ℚ),
      u ^ 2 - 2 * q * v * w = x →
      2 * u * v - 2 * p * v * w - q * w ^ 2 = -1 →
      v ^ 2 + 2 * u * w - p * w ^ 2 = 0 →
      xR = x + ((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2 →
      yR = (3 * u - 2 * p * w) * (((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2) -
        (p ^ 2 * u * w ^ 2 - p * q * v * w ^ 2 - 2 * p * u ^ 2 * w + p * u * v ^ 2 +
          q ^ 2 * w ^ 3 + 3 * q * u * v * w - q * v ^ 3 + u ^ 3) →
      yR ^ 2 = xR ^ 3 + p * xR + q ∧ (3 * xR ^ 2 + p) ^ 2 = 4 * yR ^ 2 * (x + 2 * xR) := by
    intro p q x u v w xR yR hx hE1 hE2 hxR hyR
    have hw : w ≠ 0 := by
      intro hw0
      subst hw0
      have hv2 : v ^ 2 = 0 := by linear_combination hE2
      have hv : v = 0 := pow_eq_zero_iff two_ne_zero |>.mp hv2
      subst hv
      norm_num at hE1
    have hu : u = (p * w ^ 2 - v ^ 2) / (2 * w) := by
      rw [eq_div_iff (mul_ne_zero two_ne_zero hw)]
      linear_combination hE2
    have hq : q = (1 + 2 * u * v - 2 * p * v * w) / w ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hw)]
      linear_combination (-1 : ℚ) * hE1
    subst hu
    subst hq
    subst hx
    subst hxR
    subst hyR
    constructor
    · field_simp
      ring
    · field_simp
      ring
  intro p q x y E _ ha1 ha2 ha3 ha4 ha6 h hy hw
  obtain ⟨u, v, w, hx, hE1, hE2⟩ := hw
  obtain ⟨xR, hxR⟩ : ∃ xR : ℚ, xR = x + ((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2 := ⟨_, rfl⟩
  obtain ⟨yR, hyR⟩ : ∃ yR : ℚ, yR = (3 * u - 2 * p * w) * (((3 * u - 2 * p * w) ^ 2 - 3 * x) / 2) -
      (p ^ 2 * u * w ^ 2 - p * q * v * w ^ 2 - 2 * p * u ^ 2 * w + p * u * v ^ 2 +
        q ^ 2 * w ^ 3 + 3 * q * u * v * w - q * v ^ 3 + u ^ 3) := ⟨_, rfl⟩
  obtain ⟨hcurve, hdbl⟩ := key p q x u v w xR yR hx hE1 hE2 hxR hyR
  -- the candidate R = (xR, yR) has yR ≠ 0, since E.Δ ≠ 0
  have hyR0 : yR ≠ 0 := by
    intro h0
    rw [h0] at hdbl hcurve
    have h1 : 3 * xR ^ 2 + p = 0 := by
      have h2 : (3 * xR ^ 2 + p) ^ 2 = 0 := by linear_combination hdbl
      exact pow_eq_zero_iff two_ne_zero |>.mp h2
    have h3 : xR ^ 3 + p * xR + q = 0 := by linear_combination -hcurve
    have hq : q = 2 * xR ^ 3 := by linear_combination h3 - xR * h1
    have hp : p = -3 * xR ^ 2 := by linear_combination h1
    have hΔ : E.Δ = -16 * (4 * p ^ 3 + 27 * q ^ 2) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha1, ha2, ha3, ha4, ha6]
      ring
    have hzero : 4 * p ^ 3 + 27 * q ^ 2 = 0 := by rw [hp, hq]; ring
    exact E.isUnit_Δ.ne_zero (by rw [hΔ, hzero]; ring)
  -- the candidate is a nonsingular affine point
  have heq : E.toAffine.Equation xR yR := by
    rw [WeierstrassCurve.Affine.equation_iff, ha1, ha2, ha3, ha4, ha6]
    linear_combination hcurve
  have hR : E.toAffine.Nonsingular xR yR := WeierstrassCurve.Affine.equation_iff_nonsingular.mp heq
  have hne : yR ≠ E.toAffine.negY xR yR := by
    intro h'
    apply hyR0
    simp only [WeierstrassCurve.Affine.negY, ha1, ha3, zero_mul, sub_zero] at h'
    linarith
  -- the x-coordinate of R + R is x
  have hslope : E.toAffine.slope xR xR yR yR = (3 * xR ^ 2 + p) / (2 * yR) := by
    have hd : yR - E.toAffine.negY xR yR = 2 * yR := by
      simp only [WeierstrassCurve.Affine.negY, ha1, ha3, zero_mul, sub_zero]
      ring
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hne, hd, ha1, ha2, ha4]
    ring
  have hX : E.toAffine.addX xR xR (E.toAffine.slope xR xR yR yR) = x := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX, ha1, ha2]
    have h2y : 2 * yR ≠ 0 := mul_ne_zero two_ne_zero hyR0
    field_simp
    linear_combination hdbl
  -- a point with x-coordinate x is ±P
  have fin : ∀ (X3 Y3 : ℚ) (h3 : E.toAffine.Nonsingular X3 Y3), X3 = x →
      WeierstrassCurve.Affine.Point.some _ _ h3 = WeierstrassCurve.Affine.Point.some _ _ h ∨
        WeierstrassCurve.Affine.Point.some _ _ h3 = -WeierstrassCurve.Affine.Point.some _ _ h := by
    intro X3 Y3 h3 hX3
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h3.1 h.1 hX3 with hY | hY
    · left
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX3, hY⟩
    · right
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX3, hY⟩
  obtain ⟨h3, hsum⟩ : ∃ h3 : E.toAffine.Nonsingular
      (E.toAffine.addX xR xR (E.toAffine.slope xR xR yR yR))
      (E.toAffine.addY xR xR yR (E.toAffine.slope xR xR yR yR)),
      WeierstrassCurve.Affine.Point.some _ _ hR + WeierstrassCurve.Affine.Point.some _ _ hR =
        WeierstrassCurve.Affine.Point.some _ _ h3 :=
    ⟨_, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne⟩
  rcases fin _ _ h3 hX with h4 | h4
  · exact ⟨WeierstrassCurve.Affine.Point.some _ _ hR, hsum.trans h4⟩
  · refine ⟨-WeierstrassCurve.Affine.Point.some _ _ hR, ?_⟩
    rw [← neg_add_rev, hsum, h4, neg_neg]

end MPP.Solutions.Bsd082
