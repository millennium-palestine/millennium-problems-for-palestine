import Mathlib
import MPP.Solutions.Bsd221

namespace MPP.Solutions.Bsd357

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (x y : K)
    (h : W.toAffine.Nonsingular x y),
    (6 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 →
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) ≠ 0 →
    (W.preΨ' 6).eval x = 0 := by
  intro K _ _ W x y h h6 h2
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y h with hPdef
  -- y ≠ -y, since otherwise 2 • P = 0
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply h2
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  -- bsd-221 on P: Q = P + P has x-coordinate x2 with x2 f(x) = g(x)
  obtain ⟨x2, y2, hn2, hQ, hx2⟩ := MPP.Solutions.Bsd221.main K W x y h hy
  -- 3 • Q = 6 • P = 0, so Q + Q = -Q
  have hQ6 : (P + P) + (P + P) + (P + P) = (6 : ℕ) • P := by
    rw [show (6 : ℕ) = 2 + 2 + 2 from rfl, add_nsmul, add_nsmul, two_nsmul]
  have hQneg : (P + P) + (P + P) = -(P + P) := by
    apply eq_neg_of_add_eq_zero_left
    rw [hQ6, h6]
  -- 2 • Q ≠ 0, otherwise 2 • P = 0
  have hy2 : y2 ≠ W.toAffine.negY x2 y2 := by
    intro hy2
    apply h2
    have h4 : (P + P) + (P + P) = 0 := by
      rw [hQ]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy2
    rw [h4, zero_add, h6] at hQ6
    rw [two_nsmul]
    exact hQ6
  rw [hQ] at hQneg
  rw [WeierstrassCurve.Affine.Point.neg_some] at hQneg
  -- bsd-221 on Q: its x-coordinate is x2 because Q + Q = -Q
  obtain ⟨x3, y3, hn3, hQQ, hx3⟩ := MPP.Solutions.Bsd221.main K W x2 y2 hn2 hy2
  have e := hQQ.symm.trans hQneg
  have hx3eq : x3 = x2 := (WeierstrassCurve.Affine.Point.some.inj e).1
  rw [hx3eq] at hx3
  -- curve identities: (2y + a₁x + a₃)² = f(x)
  have e1 := (W.toAffine.equation_iff x y).mp h.1
  have e2 := (W.toAffine.equation_iff x2 y2).mp hn2.1
  have hf1 : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * e1
  have hf2 : (2 * y2 + W.a₁ * x2 + W.a₃) ^ 2 = 4 * x2 ^ 3 + W.b₂ * x2 ^ 2 + 2 * W.b₄ * x2 + W.b₆ := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * e2
  -- Ψ₃(x2) = 0 and x2 f(x) = g(x)
  have hs : 3 * x2 ^ 4 + W.b₂ * x2 ^ 3 + 3 * W.b₄ * x2 ^ 2 + 3 * W.b₆ * x2 + W.b₈ = 0 := by
    linear_combination hx3 - x2 * hf2
  have hu : x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) =
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
    linear_combination hx2 - x2 * hf1
  have hR : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  -- preΨ′ 6 = Ψ₃ (preΨ′ 5 − preΨ₄²) and preΨ′ 5 = preΨ₄ Ψ₂Sq² − Ψ₃³
  have e6 : W.preΨ' 6 = W.Ψ₃ * (W.preΨ' 5 - W.preΨ₄ ^ 2) := by
    rw [show (6 : ℕ) = 2 * (0 + 3) from rfl, W.preΨ'_even 0]
    simp only [zero_add, WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
      WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_four]
    ring
  have e5 : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    have he0 : Even (0 : ℕ) := ⟨0, rfl⟩
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 from rfl, W.preΨ'_odd 0]
    simp only [zero_add, WeierstrassCurve.preΨ'_two, WeierstrassCurve.preΨ'_three,
      WeierstrassCurve.preΨ'_one, WeierstrassCurve.preΨ'_four, he0, ↓reduceIte]
    ring
  rw [e6, e5]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq]
  linear_combination (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 4 * hs - (3 * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 3 + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2 * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2 + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 3) + W.b₂ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) ^ 2 + (x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) * (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) ^ 2) + 3 * W.b₄ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 2 * ((x2 * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)) + (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈)) + 3 * W.b₆ * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) ^ 3) * hu + (-2*W.b₂^2*W.b₄*x^8 - 5*W.b₂^2*W.b₆*x^7 - 10*W.b₂*W.b₄^2*x^7 - 33*W.b₂*W.b₄*W.b₆*x^6 - 18*W.b₂*W.b₄*x^9 - 21*W.b₂*W.b₆^2*x^5 - 45*W.b₂*W.b₆*x^8 + 3*W.b₂*x^11 - 12*W.b₄^3*x^6 - 48*W.b₄^2*W.b₆*x^5 - 48*W.b₄^2*x^8 - 54*W.b₄*W.b₆^2*x^4 - 162*W.b₄*W.b₆*x^7 - 27*W.b₄*x^10 - 18*W.b₆^3*x^3 - 108*W.b₆^2*x^6 - 81*W.b₆*x^9 - W.b₈^3 + W.b₈^2*(-5*W.b₂*x^3 - 11*W.b₄*x^2 - 9*W.b₆*x - 25*x^4) + W.b₈*(-4*W.b₂^2*x^6 - 22*W.b₂*W.b₄*x^5 - 23*W.b₂*W.b₆*x^4 - 34*W.b₂*x^7 - 28*W.b₄^2*x^4 - 54*W.b₄*W.b₆*x^3 - 102*W.b₄*x^6 - 24*W.b₆^2*x^2 - 114*W.b₆*x^5 - 63*x^8) + 9*x^12) * hR

end MPP.Solutions.Bsd357
