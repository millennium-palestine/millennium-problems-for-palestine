import Mathlib
import MPP.Solutions.Bsd221
import MPP.Solutions.Bsd240

namespace MPP.Solutions.Bsd246

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
    (x y : K) (h : W.toAffine.Nonsingular x y),
    (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (W.preΨ' 5).eval x = 0 := by
  intro K _ _ W _ x y h h5
  -- a point killed by 5 and by 4 is zero
  have zero5_4 : ∀ Q : W.toAffine.Point, (5 : ℤ) • Q = 0 → (4 : ℤ) • Q = 0 → Q = 0 := by
    intro Q hQ5 hQ4
    have e : Q = (5 : ℤ) • Q - (4 : ℤ) • Q := by abel
    rw [e, hQ5, hQ4]
    simp
  -- a point killed by 5 and by 3 is zero
  have zero5_3 : ∀ Q : W.toAffine.Point, (5 : ℤ) • Q = 0 → (3 : ℤ) • Q = 0 → Q = 0 := by
    intro Q hQ5 hQ3
    have e : Q = (2 : ℤ) • ((3 : ℤ) • Q) - (5 : ℤ) • Q := by
      rw [← mul_zsmul]
      abel
    rw [e, hQ5, hQ3]
    simp
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  have hP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero h
  -- 2P is affine: 2y + a₁x + a₃ ≠ 0, since 2P = 0 would give P = 0
  have hD : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hD0
    have hyeq : y = W.toAffine.negY x y := by
      rw [WeierstrassCurve.Affine.negY]
      linear_combination hD0
    apply hP
    apply zero5_4 _ h5
    have h2 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x y h = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyeq
    have e : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) +
          (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) := by
      abel
    rw [e, h2, add_zero]
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply hD
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  -- first doubling (bsd-221): P + P = (x2, y2)
  obtain ⟨x2, y2, h2, hPP, hx2⟩ := MPP.Solutions.Bsd221.main K W x y h hyne
  have hE2 : y2 ^ 2 + W.a₁ * x2 * y2 + W.a₃ * y2 = x2 ^ 3 + W.a₂ * x2 ^ 2 + W.a₄ * x2 + W.a₆ := by
    have hx := h2.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  -- second doubling (bsd-221): (P + P) + (P + P) = (x3, y3)
  have hyne2 : y2 ≠ W.toAffine.negY x2 y2 := by
    intro hy2
    apply hP
    apply zero5_4 _ h5
    have h2' : (WeierstrassCurve.Affine.Point.some x2 y2 h2 : W.toAffine.Point) +
        WeierstrassCurve.Affine.Point.some x2 y2 h2 = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy2
    have e : (4 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) +
          (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) := by
      abel
    rw [e, hPP, h2']
  obtain ⟨x3, y3, h3, hQQ, hx3⟩ := MPP.Solutions.Bsd221.main K W x2 y2 h2 hyne2
  -- 4P = -P because 5P = 0
  have hneg : (WeierstrassCurve.Affine.Point.some x2 y2 h2 : W.toAffine.Point) +
      WeierstrassCurve.Affine.Point.some x2 y2 h2 =
      -(WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
    rw [← hPP]
    apply eq_neg_of_add_eq_zero_left
    have e : (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) +
        (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h) +
          (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) =
        (5 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
      abel
    rw [e, h5]
  have hx3eq : x3 = x := by
    have := hQQ.symm.trans hneg
    rw [WeierstrassCurve.Affine.Point.neg_some] at this
    exact (WeierstrassCurve.Affine.Point.some.inj this).1
  -- the curve identities (2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆
  have hgD : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hE
  have hgD2 : (2 * y2 + W.a₁ * x2 + W.a₃) ^ 2 =
      4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hE2
  have hH : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := W.b_relation
  have hA : x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    linear_combination hx2 - x2 * hgD
  have hB : x * (4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆) =
      x2 ^ 4 - W.b₄ * x2 ^ 2 - 2 * W.b₆ * x2 - W.b₈ := by
    linear_combination hx3 - (2 * y2 + W.a₁ * x2 + W.a₃) ^ 2 * hx3eq - x * hgD2
  -- eliminate x2: the resultant is the 5-division polynomial times Ψ₃(x)
  have key : (W.b₂^3*W.b₈*x^5 - W.b₂^2*W.b₄*W.b₆*x^5 + 5*W.b₂^2*W.b₄*W.b₈*x^4 - W.b₂^2*W.b₆^2*x^4 + 2*W.b₂^2*W.b₆*W.b₈*x^3 + 3*W.b₂^2*W.b₆*x^7 + 15*W.b₂^2*W.b₈*x^6 + W.b₂^2*x^10 - 4*W.b₂*W.b₄^2*W.b₆*x^4 + 8*W.b₂*W.b₄^2*W.b₈*x^3 - 3*W.b₂*W.b₄^2*x^7 - 6*W.b₂*W.b₄*W.b₆^2*x^3 + 6*W.b₂*W.b₄*W.b₆*W.b₈*x^2 - 8*W.b₂*W.b₄*W.b₆*x^6 + 46*W.b₂*W.b₄*W.b₈*x^5 + 10*W.b₂*W.b₄*x^9 - 2*W.b₂*W.b₆^3*x^2 + W.b₂*W.b₆^2*W.b₈*x - 14*W.b₂*W.b₆^2*x^5 + 10*W.b₂*W.b₆*W.b₈*x^4 + 38*W.b₂*W.b₆*x^8 - 3*W.b₂*W.b₈^2*x^3 + 78*W.b₂*W.b₈*x^7 + 5*W.b₂*x^11 - 4*W.b₄^3*W.b₆*x^3 + 4*W.b₄^3*W.b₈*x^2 - 7*W.b₄^3*x^6 - 8*W.b₄^2*W.b₆^2*x^2 + 4*W.b₄^2*W.b₆*W.b₈*x - 37*W.b₄^2*W.b₆*x^5 + 29*W.b₄^2*W.b₈*x^4 + 7*W.b₄^2*x^8 - 5*W.b₄*W.b₆^3*x + W.b₄*W.b₆^2*W.b₈ - 60*W.b₄*W.b₆^2*x^4 - 6*W.b₄*W.b₆*W.b₈*x^3 + 30*W.b₄*W.b₆*x^7 - 9*W.b₄*W.b₈^2*x^2 + 122*W.b₄*W.b₈*x^6 + 31*W.b₄*x^10 - W.b₆^4 - 25*W.b₆^3*x^3 - 17*W.b₆^2*W.b₈*x^2 - 15*W.b₆^2*x^6 - 9*W.b₆*W.b₈^2*x + 26*W.b₆*W.b₈*x^5 + 95*W.b₆*x^9 - W.b₈^3 - 9*W.b₈^2*x^4 + 133*W.b₈*x^8 + 5*x^12) * (W.b₂*x^3 + 3*W.b₄*x^2 + 3*W.b₆*x + W.b₈ + 3*x^4) = 0 := by
    linear_combination (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4 * hB
      - (W.b₂^4*x2*x^7 + 7*W.b₂^3*W.b₄*x2*x^6 + W.b₂^3*W.b₄*x^7 + 3*W.b₂^3*W.b₆*x2*x^5 - W.b₂^3*W.b₈*x^5 - W.b₂^3*x2^3*x^6 + 4*W.b₂^3*x2^2*x^7 + 12*W.b₂^3*x2*x^8 + W.b₂^3*x^9 + 18*W.b₂^2*W.b₄^2*x2*x^5 + 7*W.b₂^2*W.b₄^2*x^6 + 15*W.b₂^2*W.b₄*W.b₆*x2*x^4 + 6*W.b₂^2*W.b₄*W.b₆*x^5 - 5*W.b₂^2*W.b₄*W.b₈*x^4 - 6*W.b₂^2*W.b₄*x2^3*x^5 + 25*W.b₂^2*W.b₄*x2^2*x^6 + 56*W.b₂^2*W.b₄*x2*x^7 + 21*W.b₂^2*W.b₄*x^8 + 3*W.b₂^2*W.b₆^2*x2*x^3 + 2*W.b₂^2*W.b₆^2*x^4 - 2*W.b₂^2*W.b₆*W.b₈*x^3 - 3*W.b₂^2*W.b₆*x2^3*x^4 + 14*W.b₂^2*W.b₆*x2^2*x^5 + 16*W.b₂^2*W.b₆*x2*x^6 + 10*W.b₂^2*W.b₆*x^7 + W.b₂^2*W.b₈*x2^2*x^4 - 4*W.b₂^2*W.b₈*x2*x^5 - 8*W.b₂^2*W.b₈*x^6 - 12*W.b₂^2*x2^3*x^7 + 47*W.b₂^2*x2^2*x^8 + 52*W.b₂^2*x2*x^9 + 8*W.b₂^2*x^10 + 20*W.b₂*W.b₄^3*x2*x^4 + 16*W.b₂*W.b₄^3*x^5 + 24*W.b₂*W.b₄^2*W.b₆*x2*x^3 + 26*W.b₂*W.b₄^2*W.b₆*x^4 - 8*W.b₂*W.b₄^2*W.b₈*x^3 - 12*W.b₂*W.b₄^2*x2^3*x^4 + 52*W.b₂*W.b₄^2*x2^2*x^5 + 79*W.b₂*W.b₄^2*x2*x^6 + 84*W.b₂*W.b₄^2*x^7 + 9*W.b₂*W.b₄*W.b₆^2*x2*x^2 + 17*W.b₂*W.b₄*W.b₆^2*x^3 - 6*W.b₂*W.b₄*W.b₆*W.b₈*x^2 - 12*W.b₂*W.b₄*W.b₆*x2^3*x^3 + 58*W.b₂*W.b₄*W.b₆*x2^2*x^4 + 28*W.b₂*W.b₄*W.b₆*x2*x^5 + 110*W.b₂*W.b₄*W.b₆*x^6 + 4*W.b₂*W.b₄*W.b₈*x2^2*x^3 - 18*W.b₂*W.b₄*W.b₈*x2*x^4 - 16*W.b₂*W.b₄*W.b₈*x^5 - 48*W.b₂*W.b₄*x2^3*x^6 + 196*W.b₂*W.b₄*x2^2*x^7 + 130*W.b₂*W.b₄*x2*x^8 + 96*W.b₂*W.b₄*x^9 + W.b₂*W.b₆^3*x2*x + 4*W.b₂*W.b₆^3*x^2 - W.b₂*W.b₆^2*W.b₈*x - 3*W.b₂*W.b₆^2*x2^3*x^2 + 16*W.b₂*W.b₆^2*x2^2*x^3 - 8*W.b₂*W.b₆^2*x2*x^4 + 49*W.b₂*W.b₆^2*x^5 + 2*W.b₂*W.b₆*W.b₈*x2^2*x^2 - 12*W.b₂*W.b₆*W.b₈*x2*x^3 + 8*W.b₂*W.b₆*W.b₈*x^4 - 24*W.b₂*W.b₆*x2^3*x^5 + 110*W.b₂*W.b₆*x2^2*x^6 - 4*W.b₂*W.b₆*x2*x^7 + 56*W.b₂*W.b₆*x^8 - W.b₂*W.b₈^2*x2*x^2 + 4*W.b₂*W.b₈^2*x^3 + 8*W.b₂*W.b₈*x2^2*x^5 - 30*W.b₂*W.b₈*x2*x^6 - 24*W.b₂*W.b₈*x^7 - 48*W.b₂*x2^3*x^8 + 184*W.b₂*x2^2*x^9 + 95*W.b₂*x2*x^10 + 20*W.b₂*x^11 + 8*W.b₄^4*x2*x^3 + 12*W.b₄^4*x^4 + 12*W.b₄^3*W.b₆*x2*x^2 + 28*W.b₄^3*W.b₆*x^3 - 4*W.b₄^3*W.b₈*x^2 - 8*W.b₄^3*x2^3*x^3 + 36*W.b₄^3*x2^2*x^4 + 30*W.b₄^3*x2*x^5 + 93*W.b₄^3*x^6 + 6*W.b₄^2*W.b₆^2*x2*x + 27*W.b₄^2*W.b₆^2*x^2 - 4*W.b₄^2*W.b₆*W.b₈*x - 12*W.b₄^2*W.b₆*x2^3*x^2 + 60*W.b₄^2*W.b₆*x2^2*x^3 - 9*W.b₄^2*W.b₆*x2*x^4 + 198*W.b₄^2*W.b₆*x^5 + 4*W.b₄^2*W.b₈*x2^2*x^2 - 20*W.b₄^2*W.b₈*x2*x^3 + 3*W.b₄^2*W.b₈*x^4 - 48*W.b₄^2*x2^3*x^5 + 204*W.b₄^2*x2^2*x^6 + 48*W.b₄^2*x2*x^7 + 189*W.b₄^2*x^8 + W.b₄*W.b₆^3*x2 + 12*W.b₄*W.b₆^3*x - W.b₄*W.b₆^2*W.b₈ - 6*W.b₄*W.b₆^2*x2^3*x + 33*W.b₄*W.b₆^2*x2^2*x^2 - 36*W.b₄*W.b₆^2*x2*x^3 + 165*W.b₄*W.b₆^2*x^4 + 4*W.b₄*W.b₆*W.b₈*x2^2*x - 26*W.b₄*W.b₆*W.b₈*x2*x^2 + 44*W.b₄*W.b₆*W.b₈*x^3 - 48*W.b₄*W.b₆*x2^3*x^4 + 228*W.b₄*W.b₆*x2^2*x^5 - 102*W.b₄*W.b₆*x2*x^6 + 276*W.b₄*W.b₆*x^7 - 2*W.b₄*W.b₈^2*x2*x + 11*W.b₄*W.b₈^2*x^2 + 16*W.b₄*W.b₈*x2^2*x^4 - 68*W.b₄*W.b₈*x2*x^5 - 6*W.b₄*W.b₈*x^6 - 96*W.b₄*x2^3*x^7 + 384*W.b₄*x2^2*x^8 + 70*W.b₄*x2*x^9 + 123*W.b₄*x^10 + 2*W.b₆^4 - W.b₆^3*x2^3 + 6*W.b₆^3*x2^2*x - 12*W.b₆^3*x2*x^2 + 48*W.b₆^3*x^3 + W.b₆^2*W.b₈*x2^2 - 8*W.b₆^2*W.b₈*x2*x + 28*W.b₆^2*W.b₈*x^2 - 12*W.b₆^2*x2^3*x^3 + 63*W.b₆^2*x2^2*x^4 - 72*W.b₆^2*x2*x^5 + 132*W.b₆^2*x^6 - W.b₆*W.b₈^2*x2 + 10*W.b₆*W.b₈^2*x + 8*W.b₆*W.b₈*x2^2*x^3 - 46*W.b₆*W.b₈*x2*x^4 + 44*W.b₆*W.b₈*x^5 - 48*W.b₆*x2^3*x^6 + 216*W.b₆*x2^2*x^7 - 81*W.b₆*x2*x^8 + 74*W.b₆*x^9 + W.b₈^3 - 4*W.b₈^2*x2*x^3 + 13*W.b₈^2*x^4 + 16*W.b₈*x2^2*x^6 - 56*W.b₈*x2*x^7 - 29*W.b₈*x^8 - 64*x2^3*x^9 + 240*x2^2*x^10 + 60*x2*x^11 + 15*x^12) * hA - (-W.b₂^3*x^9 - 7*W.b₂^2*W.b₄*x^8 - 5*W.b₂^2*W.b₆*x^7 - W.b₂^2*W.b₈*x^6 - 11*W.b₂^2*x^10 - 16*W.b₂*W.b₄^2*x^7 - 22*W.b₂*W.b₄*W.b₆*x^6 - 4*W.b₂*W.b₄*W.b₈*x^5 - 52*W.b₂*W.b₄*x^9 - 7*W.b₂*W.b₆^2*x^5 - 2*W.b₂*W.b₆*W.b₈*x^4 - 38*W.b₂*W.b₆*x^8 - 8*W.b₂*W.b₈*x^7 - 40*W.b₂*x^11 - 12*W.b₄^3*x^6 - 24*W.b₄^2*W.b₆*x^5 - 4*W.b₄^2*W.b₈*x^4 - 60*W.b₄^2*x^8 - 15*W.b₄*W.b₆^2*x^4 - 4*W.b₄*W.b₆*W.b₈*x^3 - 84*W.b₄*W.b₆*x^7 - 16*W.b₄*W.b₈*x^6 - 96*W.b₄*x^10 - 3*W.b₆^3*x^3 - W.b₆^2*W.b₈*x^2 - 27*W.b₆^2*x^6 - 8*W.b₆*W.b₈*x^5 - 72*W.b₆*x^9 - 16*W.b₈*x^8 - 48*x^12) * hH
  -- Ψ₃(x) ≠ 0, otherwise 3P = 0 (bsd-240) and then P = 0
  have hΨne : (W.b₂*x^3 + 3*W.b₄*x^2 + 3*W.b₆*x + W.b₈ + 3*x^4) ≠ 0 := by
    intro h0
    apply hP
    apply zero5_3 _ h5
    exact MPP.Solutions.Bsd240.main K W x y h hD (by linear_combination h0)
  have hF := (mul_eq_zero.mp key).resolve_right hΨne
  have h5eq : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    have h := W.preΨ'_odd 0
    norm_num at h
    linear_combination h
  rw [h5eq]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  simp [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq]
  linear_combination hF

end MPP.Solutions.Bsd246
