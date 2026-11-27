import Mathlib
import MPP.Solutions.Bsd221
import MPP.Solutions.Bsd355

namespace MPP.Solutions.Bsd359

-- the curve identity (2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆ at an affine point
lemma sq_eq_cubic {K : Type} [Field K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    have hx := h.1
    rw [WeierstrassCurve.Affine.equation_iff] at hx
    exact hx
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination 4 * hE

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    (8 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 →
    (W.preΨ' 8).eval x = 0 := by
  intro K _ _ W x y h h8 h2
  -- the recursion preΨ'₈ = preΨ₄ (Ψ₃² preΨ'₆ − preΨ'₅²), and preΨ'₅, preΨ'₆ in terms of preΨ₄, Ψ₃
  have h5 : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    have h := W.preΨ'_odd 0
    norm_num at h
    linear_combination h
  have h6' : W.preΨ' 6 = W.Ψ₃ * (W.preΨ' 5 - W.preΨ₄ ^ 2) := by
    have h := W.preΨ'_even 0
    norm_num at h
    linear_combination h
  have h8' : W.preΨ' 8 = W.preΨ₄ * (W.Ψ₃ ^ 2 * W.preΨ' 6 - W.preΨ' 5 ^ 2) := by
    have h := W.preΨ'_even 1
    norm_num at h
    linear_combination h
  have h8eval : (W.preΨ' 8).eval x = W.preΨ₄.eval x *
      ((W.Ψ₃.eval x) ^ 2 * (W.preΨ' 6).eval x - (W.preΨ' 5).eval x ^ 2) := by
    rw [h8']
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]
  -- the 4-torsion instance (bsd-355) for 2P when 4P = 0
  by_cases h4P : (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0
  · have hp4 := MPP.Solutions.Bsd355.main K W x y h h4P h2
    rw [W.preΨ'_four] at hp4
    rw [h8eval, hp4, zero_mul]
  -- otherwise 2P has order 8 or 4 with 4 • (2P) = 8P = 0 and 2 • (2P) = 4P ≠ 0
  have hyne : y ≠ W.toAffine.negY x y := by
    intro hy
    apply h2
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  obtain ⟨x2, y2, h2', hPP, hx2⟩ := MPP.Solutions.Bsd221.main K W x y h hyne
  have hgD : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ :=
    sq_eq_cubic W x y h
  have hA : x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    linear_combination hx2 - x2 * hgD
  have hQ4 : (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x2 y2 h2' : W.toAffine.Point) = 0 := by
    rw [← hPP]
    have e : (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h :
        W.toAffine.Point) = (8 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
      abel
    rw [e]
    exact h8
  have hQ2 : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x2 y2 h2' : W.toAffine.Point) ≠ 0 := by
    rw [← hPP]
    have e : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x y h :
        W.toAffine.Point) = (4 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) := by
      abel
    rw [e]
    exact h4P
  -- Q = 2P has 4 • Q = 0 and 2 • Q ≠ 0, so preΨ₄(x2) = 0 by bsd-355
  have hq := MPP.Solutions.Bsd355.main K W x2 y2 h2' hQ4 hQ2
  rw [W.preΨ'_four] at hq
  have hq' : 2 * x2 ^ 6 + W.b₂ * x2 ^ 5 + 5 * W.b₄ * x2 ^ 4 + 10 * W.b₆ * x2 ^ 3 + 10 * W.b₈ * x2 ^ 2
      + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x2 + (W.b₄ * W.b₈ - W.b₆ ^ 2) = 0 := by
    simp only [WeierstrassCurve.preΨ₄, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat] at hq
    linear_combination hq
  -- the resultant: with u = x2 f and g = x⁴ − b₄x² − 2b₆x − b₈, P₄(u) = f⁶ preΨ₄(x2) = 0 and P₄(u) − P₄(g) = (u − g) T
  have hP4 : 2 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 6
      + W.b₂ * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 5 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      + 5 * W.b₄ * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 4 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2
      + 10 * W.b₆ * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3
      + 10 * W.b₈ * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4
      + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 5
      + (W.b₄ * W.b₈ - W.b₆ ^ 2) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 6 = 0 := by
    linear_combination (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 6 * hq'
  have hR : 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 6
      + W.b₂ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 5 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
      + 5 * W.b₄ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 4 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2
      + 10 * W.b₆ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3
      + 10 * W.b₈ * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4
      + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 5
      + (W.b₄ * W.b₈ - W.b₆ ^ 2) * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 6 = 0 := by
    linear_combination hP4 - (W.b₂ * W.b₈ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 5
      + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 4
      + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
      + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2
      + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3
      + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
        * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 4
      - W.b₄ * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 5
      + 5 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3
      + 5 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2
        * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
      + 5 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)
        * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2
      + 5 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3
      + 10 * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2
      + 10 * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)
        * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
      + 10 * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2
      + 10 * W.b₈ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)
      + 10 * W.b₈ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
      + 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 5
      + 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 4 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆))
      + 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2
      + 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3
      + 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 4
      + 2 * (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 5) * hA
  have hH : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := W.b_relation
  -- C₈ = R₈ − E₈ (4b₈ − b₂b₆ + b₄²), where R₈ = P₄(g) and C₈ = Ψ₃² preΨ'₆ − preΨ'₅²
  have hC : (W.Ψ₃.eval x) ^ 2 * (W.preΨ' 6).eval x - (W.preΨ' 5).eval x ^ 2 = 0 := by
    rw [h6', h5]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, WeierstrassCurve.preΨ₄,
      WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    linear_combination hR - (W.b₂^5*W.b₆*x^12 + 2*W.b₂^5*W.b₈*x^11 + 10*W.b₂^4*W.b₄*W.b₆*x^11 + 20*W.b₂^4*W.b₄*W.b₈*x^10 + 6*W.b₂^4*W.b₆^2*x^10 + 12*W.b₂^4*W.b₆*W.b₈*x^9 + 23*W.b₂^4*W.b₆*x^13 + W.b₂^4*W.b₈^2*x^8 + 44*W.b₂^4*W.b₈*x^12 + 3*W.b₂^4*x^16 + 40*W.b₂^3*W.b₄^2*W.b₆*x^10 + 80*W.b₂^3*W.b₄^2*W.b₈*x^9 + 48*W.b₂^3*W.b₄*W.b₆^2*x^9 + 96*W.b₂^3*W.b₄*W.b₆*W.b₈*x^8 + 187*W.b₂^3*W.b₄*W.b₆*x^12 + 8*W.b₂^3*W.b₄*W.b₈^2*x^7 + 358*W.b₂^3*W.b₄*W.b₈*x^11 + 34*W.b₂^3*W.b₄*x^15 + 14*W.b₂^3*W.b₆^3*x^8 + 28*W.b₂^3*W.b₆^2*W.b₈*x^7 + 115*W.b₂^3*W.b₆^2*x^11 + 4*W.b₂^3*W.b₆*W.b₈^2*x^6 + 225*W.b₂^3*W.b₆*W.b₈*x^10 + 239*W.b₂^3*W.b₆*x^14 + 23*W.b₂^3*W.b₈^2*x^9 + 390*W.b₂^3*W.b₈*x^13 + 39*W.b₂^3*x^17 + 80*W.b₂^2*W.b₄^3*W.b₆*x^9 + 160*W.b₂^2*W.b₄^3*W.b₈*x^8 + 4*W.b₂^2*W.b₄^3*x^12 + 144*W.b₂^2*W.b₄^2*W.b₆^2*x^8 + 288*W.b₂^2*W.b₄^2*W.b₆*W.b₈*x^7 + 597*W.b₂^2*W.b₄^2*W.b₆*x^11 + 24*W.b₂^2*W.b₄^2*W.b₈^2*x^6 + 1110*W.b₂^2*W.b₄^2*W.b₈*x^10 + 138*W.b₂^2*W.b₄^2*x^14 + 84*W.b₂^2*W.b₄*W.b₆^3*x^7 + 168*W.b₂^2*W.b₄*W.b₆^2*W.b₈*x^6 + 762*W.b₂^2*W.b₄*W.b₆^2*x^10 + 24*W.b₂^2*W.b₄*W.b₆*W.b₈^2*x^5 + 1452*W.b₂^2*W.b₄*W.b₆*W.b₈*x^9 + 1524*W.b₂^2*W.b₄*W.b₆*x^13 + 165*W.b₂^2*W.b₄*W.b₈^2*x^8 + 2418*W.b₂^2*W.b₄*W.b₈*x^12 + 333*W.b₂^2*W.b₄*x^16 + 16*W.b₂^2*W.b₆^4*x^6 + 32*W.b₂^2*W.b₆^3*W.b₈*x^5 + 257*W.b₂^2*W.b₆^3*x^9 + 6*W.b₂^2*W.b₆^2*W.b₈^2*x^4 + 510*W.b₂^2*W.b₆^2*W.b₈*x^8 + 900*W.b₂^2*W.b₆^2*x^12 + 132*W.b₂^2*W.b₆*W.b₈^2*x^7 + 1572*W.b₂^2*W.b₆*W.b₈*x^11 + 1228*W.b₂^2*W.b₆*x^15 + 13*W.b₂^2*W.b₈^3*x^6 + 177*W.b₂^2*W.b₈^2*x^10 + 1715*W.b₂^2*W.b₈*x^14 + 191*W.b₂^2*x^18 + 80*W.b₂*W.b₄^4*W.b₆*x^8 + 160*W.b₂*W.b₄^4*W.b₈*x^7 + 18*W.b₂*W.b₄^4*x^11 + 192*W.b₂*W.b₄^3*W.b₆^2*x^7 + 384*W.b₂*W.b₄^3*W.b₆*W.b₈*x^6 + 905*W.b₂*W.b₄^3*W.b₆*x^10 + 32*W.b₂*W.b₄^3*W.b₈^2*x^5 + 1562*W.b₂*W.b₄^3*W.b₈*x^9 + 278*W.b₂*W.b₄^3*x^13 + 168*W.b₂*W.b₄^2*W.b₆^3*x^6 + 336*W.b₂*W.b₄^2*W.b₆^2*W.b₈*x^5 + 1779*W.b₂*W.b₄^2*W.b₆^2*x^9 + 48*W.b₂*W.b₄^2*W.b₆*W.b₈^2*x^4 + 3213*W.b₂*W.b₄^2*W.b₆*W.b₈*x^8 + 3495*W.b₂*W.b₄^2*W.b₆*x^12 + 405*W.b₂*W.b₄^2*W.b₈^2*x^7 + 5154*W.b₂*W.b₄^2*W.b₈*x^11 + 885*W.b₂*W.b₄^2*x^15 + 64*W.b₂*W.b₄*W.b₆^4*x^5 + 128*W.b₂*W.b₄*W.b₆^3*W.b₈*x^4 + 1251*W.b₂*W.b₄*W.b₆^3*x^8 + 24*W.b₂*W.b₄*W.b₆^2*W.b₈^2*x^3 + 2388*W.b₂*W.b₄*W.b₆^2*W.b₈*x^7 + 4332*W.b₂*W.b₄*W.b₆^2*x^11 + 681*W.b₂*W.b₄*W.b₆*W.b₈^2*x^6 + 7182*W.b₂*W.b₄*W.b₆*W.b₈*x^10 + 5329*W.b₂*W.b₄*W.b₆*x^14 + 72*W.b₂*W.b₄*W.b₈^3*x^5 + 936*W.b₂*W.b₄*W.b₈^2*x^9 + 7136*W.b₂*W.b₄*W.b₈*x^13 + 1104*W.b₂*W.b₄*x^17 + 9*W.b₂*W.b₆^5*x^4 + 18*W.b₂*W.b₆^4*W.b₈*x^3 + 313*W.b₂*W.b₆^4*x^7 + 4*W.b₂*W.b₆^3*W.b₈^2*x^2 + 649*W.b₂*W.b₆^3*W.b₈*x^6 + 1543*W.b₂*W.b₆^3*x^10 + 312*W.b₂*W.b₆^2*W.b₈^2*x^5 + 2820*W.b₂*W.b₆^2*W.b₈*x^9 + 2976*W.b₂*W.b₆^2*x^13 + 73*W.b₂*W.b₆*W.b₈^3*x^4 + 873*W.b₂*W.b₆*W.b₈^2*x^8 + 4683*W.b₂*W.b₆*W.b₈*x^12 + 3043*W.b₂*W.b₆*x^16 + 7*W.b₂*W.b₈^4*x^3 + 104*W.b₂*W.b₈^3*x^7 + 538*W.b₂*W.b₈^2*x^11 + 3736*W.b₂*W.b₈*x^15 + 415*W.b₂*x^19 + 32*W.b₄^5*W.b₆*x^7 + 64*W.b₄^5*W.b₈*x^6 + 20*W.b₄^5*x^10 + 96*W.b₄^4*W.b₆^2*x^6 + 192*W.b₄^4*W.b₆*W.b₈*x^5 + 552*W.b₄^4*W.b₆*x^9 + 16*W.b₄^4*W.b₈^2*x^4 + 844*W.b₄^4*W.b₈*x^8 + 240*W.b₄^4*x^12 + 112*W.b₄^3*W.b₆^3*x^5 + 224*W.b₄^3*W.b₆^2*W.b₈*x^4 + 1452*W.b₄^3*W.b₆^2*x^8 + 32*W.b₄^3*W.b₆*W.b₈^2*x^3 + 2430*W.b₄^3*W.b₆*W.b₈*x^7 + 2946*W.b₄^3*W.b₆*x^11 + 335*W.b₄^3*W.b₈^2*x^6 + 3814*W.b₄^3*W.b₈*x^10 + 823*W.b₄^3*x^14 + 64*W.b₄^2*W.b₆^4*x^4 + 128*W.b₄^2*W.b₆^3*W.b₈*x^3 + 1564*W.b₄^2*W.b₆^3*x^7 + 24*W.b₄^2*W.b₆^2*W.b₈^2*x^2 + 2838*W.b₄^2*W.b₆^2*W.b₈*x^6 + 5658*W.b₄^2*W.b₆^2*x^10 + 867*W.b₄^2*W.b₆*W.b₈^2*x^5 + 8622*W.b₄^2*W.b₆*W.b₈*x^9 + 6259*W.b₄^2*W.b₆*x^13 + 95*W.b₄^2*W.b₈^3*x^4 + 1275*W.b₄^2*W.b₈^2*x^8 + 7721*W.b₄^2*W.b₈*x^12 + 1453*W.b₄^2*x^16 + 18*W.b₄*W.b₆^5*x^3 + 36*W.b₄*W.b₆^4*W.b₈*x^2 + 792*W.b₄*W.b₆^4*x^6 + 8*W.b₄*W.b₆^3*W.b₈^2*x + 1586*W.b₄*W.b₆^3*W.b₈*x^5 + 4230*W.b₄*W.b₆^3*x^9 + 789*W.b₄*W.b₆^2*W.b₈^2*x^4 + 7314*W.b₄*W.b₆^2*W.b₈*x^8 + 7389*W.b₄*W.b₆^2*x^12 + 184*W.b₄*W.b₆*W.b₈^3*x^3 + 2472*W.b₄*W.b₆*W.b₈^2*x^7 + 11040*W.b₄*W.b₆*W.b₈*x^11 + 6624*W.b₄*W.b₆*x^15 + 17*W.b₄*W.b₈^4*x^2 + 304*W.b₄*W.b₈^3*x^6 + 1502*W.b₄*W.b₈^2*x^10 + 7760*W.b₄*W.b₈*x^14 + 1233*W.b₄*x^18 + 2*W.b₆^6*x^2 + 4*W.b₆^5*W.b₈*x + 156*W.b₆^5*x^5 + W.b₆^4*W.b₈^2 + 348*W.b₆^4*W.b₈*x^4 + 1155*W.b₆^4*x^8 + 241*W.b₆^3*W.b₈^2*x^3 + 2282*W.b₆^3*W.b₈*x^7 + 2641*W.b₆^3*x^11 + 85*W.b₆^2*W.b₈^3*x^2 + 1257*W.b₆^2*W.b₈^2*x^6 + 4555*W.b₆^2*W.b₈*x^10 + 3495*W.b₆^2*x^14 + 15*W.b₆*W.b₈^4*x + 320*W.b₆*W.b₈^3*x^5 + 1498*W.b₆*W.b₈^2*x^9 + 5040*W.b₆*W.b₈*x^13 + 2919*W.b₆*x^17 + W.b₈^5 + 31*W.b₈^4*x^4 + 190*W.b₈^3*x^8 + 562*W.b₈^2*x^12 + 3233*W.b₈*x^16 + 335*x^20) * hH
  rw [h8eval, hC, mul_zero]

end MPP.Solutions.Bsd359
