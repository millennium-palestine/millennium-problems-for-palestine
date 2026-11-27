import Mathlib

namespace MPP.Solutions.Bsd395

-- substitute x = G / F into a quartic relation: if x F = G and z₄ x⁴ + … + z₀ = 0,
-- then the homogenised relation z₄ G⁴ + z₃ G³ F + … + z₀ F⁴ = 0 holds
lemma homogenise {R : Type} [CommRing R] (x F G z₄ z₃ z₂ z₁ z₀ : R) (h : x * F = G)
    (hz : z₄ * x ^ 4 + z₃ * x ^ 3 + z₂ * x ^ 2 + z₁ * x + z₀ = 0) :
    z₄ * G ^ 4 + z₃ * G ^ 3 * F + z₂ * G ^ 2 * F ^ 2 + z₁ * G * F ^ 3 + z₀ * F ^ 4 = 0 := by
  linear_combination F ^ 4 * hz -
    (z₄ * ((x * F) ^ 3 + (x * F) ^ 2 * G + (x * F) * G ^ 2 + G ^ 3) +
      z₃ * F * ((x * F) ^ 2 + (x * F) * G + G ^ 2) + z₂ * F ^ 2 * (x * F + G) + z₁ * F ^ 3) * h

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (u x₂ x₃ x₄ : K),
    W.Ψ₂Sq.eval u ≠ 0 →
    x₂ * W.Ψ₂Sq.eval u = u ^ 4 - W.b₄ * u ^ 2 - 2 * W.b₆ * u - W.b₈ →
    x₄ * W.Ψ₂Sq.eval x₂ = x₂ ^ 4 - W.b₄ * x₂ ^ 2 - 2 * W.b₆ * x₂ - W.b₈ →
    x₃ * (W.Ψ₃.eval u) ^ 2 = u * (W.Ψ₃.eval u) ^ 2 - W.Ψ₂Sq.eval u * W.preΨ₄.eval u →
    x₃ = x₄ →
    (W.preΨ' 7).eval u = 0 := by
  intro K _ W u x₂ x₃ x₄ _ h2 h4 h3 h34
  have e5 : W.preΨ' 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 from rfl, W.preΨ'_odd 0]
    simp
  have e7 : W.preΨ' 7 = (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) * W.Ψ₃ ^ 3 - W.preΨ₄ ^ 3 * W.Ψ₂Sq ^ 2 := by
    rw [show (7 : ℕ) = 2 * (1 + 2) + 1 from rfl, W.preΨ'_odd 1]
    simp [e5]
  rw [e7]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_C, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq] at h2 h4 h3 ⊢
  -- Z(x₂) := (g(x₂) − u f(x₂)) D + f(x₂) F P = 0, from the triple identity and x₃ = x₄
  have hZ : (x₂ ^ 4 - W.b₄ * x₂ ^ 2 - 2 * W.b₆ * x₂ - W.b₈ -
        u * (4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆)) *
      (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2 +
      (4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆) *
        (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆) *
        (2 * u ^ 6 + W.b₂ * u ^ 5 + 5 * W.b₄ * u ^ 4 + 10 * W.b₆ * u ^ 3 + 10 * W.b₈ * u ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u + (W.b₄ * W.b₈ - W.b₆ ^ 2)) = 0 := by
    linear_combination (4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆) * h3
      - (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2 * h4
      - (4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆) *
        (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2 * h34
  -- eliminate x₂ using x₂ F = G, with F = Ψ₂Sq(u), G = g(u), D = Ψ₃(u)², P = preΨ₄(u)
  have key := homogenise x₂ (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆)
    (u ^ 4 - W.b₄ * u ^ 2 - 2 * W.b₆ * u - W.b₈)
    ((3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2)
    (-(4 * u) * (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2 +
      4 * (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆) *
        (2 * u ^ 6 + W.b₂ * u ^ 5 + 5 * W.b₄ * u ^ 4 + 10 * W.b₆ * u ^ 3 + 10 * W.b₈ * u ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u + (W.b₄ * W.b₈ - W.b₆ ^ 2)))
    (-((W.b₄ + u * W.b₂) * (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2) +
      W.b₂ * (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆) *
        (2 * u ^ 6 + W.b₂ * u ^ 5 + 5 * W.b₄ * u ^ 4 + 10 * W.b₆ * u ^ 3 + 10 * W.b₈ * u ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u + (W.b₄ * W.b₈ - W.b₆ ^ 2)))
    (-(2 * (W.b₆ + u * W.b₄)) * (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2 +
      2 * W.b₄ * (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆) *
        (2 * u ^ 6 + W.b₂ * u ^ 5 + 5 * W.b₄ * u ^ 4 + 10 * W.b₆ * u ^ 3 + 10 * W.b₈ * u ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u + (W.b₄ * W.b₈ - W.b₆ ^ 2)))
    (-((W.b₈ + u * W.b₆) * (3 * u ^ 4 + W.b₂ * u ^ 3 + 3 * W.b₄ * u ^ 2 + 3 * W.b₆ * u + W.b₈) ^ 2) +
      W.b₆ * (4 * u ^ 3 + W.b₂ * u ^ 2 + 2 * W.b₄ * u + W.b₆) *
        (2 * u ^ 6 + W.b₂ * u ^ 5 + 5 * W.b₄ * u ^ 4 + 10 * W.b₆ * u ^ 3 + 10 * W.b₈ * u ^ 2 +
          (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u + (W.b₄ * W.b₈ - W.b₆ ^ 2)))
    h2 (by linear_combination hZ)
  -- ψ₇ + (homogenised sum) = q · (4 b₈ − b₂ b₆ + b₄²), with q an integer polynomial (sympy)
  have hH : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  linear_combination -key + (-W.b₂^5*W.b₈*u^11 + W.b₂^4*W.b₄*W.b₆*u^11 - 11*W.b₂^4*W.b₄*W.b₈*u^10 - 2*W.b₂^4*W.b₄*u^14 + W.b₂^4*W.b₆^2*u^10 - 9*W.b₂^4*W.b₆*W.b₈*u^9 - 8*W.b₂^4*W.b₆*u^13 - 4*W.b₂^4*W.b₈^2*u^8 - 27*W.b₂^4*W.b₈*u^12 - W.b₂^4*u^16 + 10*W.b₂^3*W.b₄^2*W.b₆*u^10 - 46*W.b₂^3*W.b₄^2*W.b₈*u^9 - 19*W.b₂^3*W.b₄^2*u^13 + 19*W.b₂^3*W.b₄*W.b₆^2*u^9 - 65*W.b₂^3*W.b₄*W.b₆*W.b₈*u^8 - 77*W.b₂^3*W.b₄*W.b₆*u^12 - 28*W.b₂^3*W.b₄*W.b₈^2*u^7 - 254*W.b₂^3*W.b₄*W.b₈*u^11 - 46*W.b₂^3*W.b₄*u^15 + 9*W.b₂^3*W.b₆^3*u^8 - 18*W.b₂^3*W.b₆^2*W.b₈*u^7 - 50*W.b₂^3*W.b₆^2*u^11 - 14*W.b₂^3*W.b₆*W.b₈^2*u^6 - 238*W.b₂^3*W.b₆*W.b₈*u^10 - 144*W.b₂^3*W.b₆*u^14 - W.b₂^3*W.b₈^3*u^5 - 92*W.b₂^3*W.b₈^2*u^9 - 273*W.b₂^3*W.b₈*u^13 - 10*W.b₂^3*u^17 + 36*W.b₂^2*W.b₄^3*W.b₆*u^9 - 92*W.b₂^2*W.b₄^3*W.b₈*u^8 - 65*W.b₂^2*W.b₄^3*u^12 + 96*W.b₂^2*W.b₄^2*W.b₆^2*u^8 - 168*W.b₂^2*W.b₄^2*W.b₆*W.b₈*u^7 - 245*W.b₂^2*W.b₄^2*W.b₆*u^11 - 72*W.b₂^2*W.b₄^2*W.b₈^2*u^6 - 845*W.b₂^2*W.b₄^2*W.b₈*u^10 - 303*W.b₂^2*W.b₄^2*u^14 + 82*W.b₂^2*W.b₄*W.b₆^3*u^7 - 78*W.b₂^2*W.b₄*W.b₆^2*W.b₈*u^6 - 220*W.b₂^2*W.b₄*W.b₆^2*u^10 - 69*W.b₂^2*W.b₄*W.b₆*W.b₈^2*u^5 - 1384*W.b₂^2*W.b₄*W.b₆*W.b₈*u^9 - 1215*W.b₂^2*W.b₄*W.b₆*u^13 - 5*W.b₂^2*W.b₄*W.b₈^3*u^4 - 498*W.b₂^2*W.b₄*W.b₈^2*u^8 - 2049*W.b₂^2*W.b₄*W.b₈*u^12 - 304*W.b₂^2*W.b₄*u^16 + 22*W.b₂^2*W.b₆^4*u^6 - 7*W.b₂^2*W.b₆^3*W.b₈*u^5 - 33*W.b₂^2*W.b₆^3*u^9 - 15*W.b₂^2*W.b₆^2*W.b₈^2*u^4 - 452*W.b₂^2*W.b₆^2*W.b₈*u^8 - 841*W.b₂^2*W.b₆^2*u^12 - 2*W.b₂^2*W.b₆*W.b₈^3*u^3 - 261*W.b₂^2*W.b₆*W.b₈^2*u^7 - 2120*W.b₂^2*W.b₆*W.b₈*u^11 - 889*W.b₂^2*W.b₆*u^15 - 17*W.b₂^2*W.b₈^3*u^6 - 757*W.b₂^2*W.b₈^2*u^10 - 1291*W.b₂^2*W.b₈*u^14 - 31*W.b₂^2*u^18 + 56*W.b₂*W.b₄^4*W.b₆*u^8 - 88*W.b₂*W.b₄^4*W.b₈*u^7 - 96*W.b₂*W.b₄^4*u^11 + 188*W.b₂*W.b₄^3*W.b₆^2*u^7 - 180*W.b₂*W.b₄^3*W.b₆*W.b₈*u^6 - 310*W.b₂*W.b₄^3*W.b₆*u^10 - 80*W.b₂*W.b₄^3*W.b₈^2*u^5 - 1196*W.b₂*W.b₄^3*W.b₈*u^9 - 684*W.b₂*W.b₄^3*u^13 + 226*W.b₂*W.b₄^2*W.b₆^3*u^6 - 90*W.b₂*W.b₄^2*W.b₆^2*W.b₈*u^5 - 221*W.b₂*W.b₄^2*W.b₆^2*u^9 - 108*W.b₂*W.b₄^2*W.b₆*W.b₈^2*u^4 - 2618*W.b₂*W.b₄^2*W.b₆*W.b₈*u^8 - 3058*W.b₂*W.b₄^2*W.b₆*u^12 - 8*W.b₂*W.b₄^2*W.b₈^3*u^3 - 888*W.b₂*W.b₄^2*W.b₈^2*u^7 - 4768*W.b₂*W.b₄^2*W.b₈*u^11 - 1360*W.b₂*W.b₄^2*u^15 + 115*W.b₂*W.b₄*W.b₆^4*u^5 + 7*W.b₂*W.b₄*W.b₆^3*W.b₈*u^4 + 67*W.b₂*W.b₄*W.b₆^3*u^8 - 42*W.b₂*W.b₄*W.b₆^2*W.b₈^2*u^3 - 1582*W.b₂*W.b₄*W.b₆^2*W.b₈*u^7 - 3432*W.b₂*W.b₄*W.b₆^2*u^11 - 6*W.b₂*W.b₄*W.b₆*W.b₈^3*u^2 - 912*W.b₂*W.b₄*W.b₆*W.b₈^2*u^6 - 8566*W.b₂*W.b₄*W.b₆*W.b₈*u^10 - 5444*W.b₂*W.b₄*W.b₆*u^14 - 60*W.b₂*W.b₄*W.b₈^3*u^5 - 2788*W.b₂*W.b₄*W.b₈^2*u^9 - 6884*W.b₂*W.b₄*W.b₈*u^13 - 764*W.b₂*W.b₄*u^17 + 21*W.b₂*W.b₆^5*u^4 + 9*W.b₂*W.b₆^4*W.b₈*u^3 + 60*W.b₂*W.b₆^4*u^7 - 4*W.b₂*W.b₆^3*W.b₈^2*u^2 - 274*W.b₂*W.b₆^3*W.b₈*u^6 - 942*W.b₂*W.b₆^3*u^10 - W.b₂*W.b₆^2*W.b₈^3*u - 222*W.b₂*W.b₆^2*W.b₈^2*u^5 - 3005*W.b₂*W.b₆^2*W.b₈*u^9 - 3948*W.b₂*W.b₆^2*u^13 - 26*W.b₂*W.b₆*W.b₈^3*u^4 - 1490*W.b₂*W.b₆*W.b₈^2*u^8 - 7774*W.b₂*W.b₆*W.b₈*u^12 - 2262*W.b₂*W.b₆*u^16 - 88*W.b₂*W.b₈^3*u^7 - 2664*W.b₂*W.b₈^2*u^11 - 2856*W.b₂*W.b₈*u^15 - 24*W.b₂*u^19 + 32*W.b₄^5*W.b₆*u^7 - 32*W.b₄^5*W.b₈*u^6 - 52*W.b₄^5*u^10 + 128*W.b₄^4*W.b₆^2*u^6 - 64*W.b₄^4*W.b₆*W.b₈*u^5 - 128*W.b₄^4*W.b₆*u^9 - 32*W.b₄^4*W.b₈^2*u^4 - 612*W.b₄^4*W.b₈*u^8 - 508*W.b₄^4*u^12 + 196*W.b₄^3*W.b₆^3*u^5 - 12*W.b₄^3*W.b₆^2*W.b₈*u^4 + 39*W.b₄^3*W.b₆^2*u^8 - 52*W.b₄^3*W.b₆*W.b₈^2*u^3 - 1604*W.b₄^3*W.b₆*W.b₈*u^7 - 2400*W.b₄^3*W.b₆*u^11 - 4*W.b₄^3*W.b₈^3*u^2 - 520*W.b₄^3*W.b₈^2*u^6 - 3524*W.b₄^3*W.b₈*u^10 - 1568*W.b₄^3*u^14 + 144*W.b₄^2*W.b₆^4*u^4 + 44*W.b₄^2*W.b₆^3*W.b₈*u^3 + 297*W.b₄^2*W.b₆^3*u^7 - 24*W.b₄^2*W.b₆^2*W.b₈^2*u^2 - 1325*W.b₄^2*W.b₆^2*W.b₈*u^6 - 3375*W.b₄^2*W.b₆^2*u^10 - 4*W.b₄^2*W.b₆*W.b₈^3*u - 780*W.b₄^2*W.b₆*W.b₈^2*u^5 - 8500*W.b₄^2*W.b₆*W.b₈*u^9 - 7308*W.b₄^2*W.b₆*u^13 - 52*W.b₄^2*W.b₈^3*u^4 - 2548*W.b₄^2*W.b₈^2*u^8 - 8364*W.b₄^2*W.b₈*u^12 - 1836*W.b₄^2*u^16 + 51*W.b₄*W.b₆^5*u^3 + 31*W.b₄*W.b₆^4*W.b₈*u^2 + 228*W.b₄*W.b₆^4*u^6 - W.b₄*W.b₆^3*W.b₈^2*u - 404*W.b₄*W.b₆^3*W.b₈*u^5 - 1623*W.b₄*W.b₆^3*u^9 - W.b₄*W.b₆^2*W.b₈^3 - 366*W.b₄*W.b₆^2*W.b₈^2*u^4 - 5637*W.b₄*W.b₆^2*W.b₈*u^8 - 8724*W.b₄*W.b₆^2*u^12 - 44*W.b₄*W.b₆*W.b₈^3*u^3 - 2692*W.b₄*W.b₆*W.b₈^2*u^7 - 16148*W.b₄*W.b₆*W.b₈*u^11 - 7548*W.b₄*W.b₆*u^15 - 160*W.b₄*W.b₈^3*u^6 - 4976*W.b₄*W.b₈^2*u^10 - 8192*W.b₄*W.b₈*u^14 - 624*W.b₄*u^18 + 7*W.b₆^6*u^2 + 6*W.b₆^5*W.b₈*u + 51*W.b₆^5*u^5 + W.b₆^4*W.b₈^2 - 33*W.b₆^4*W.b₈*u^4 - 228*W.b₆^4*u^8 - 53*W.b₆^3*W.b₈^2*u^3 - 1110*W.b₆^3*W.b₈*u^7 - 2605*W.b₆^3*u^11 - 9*W.b₆^2*W.b₈^3*u^2 - 685*W.b₆^2*W.b₈^2*u^6 - 5907*W.b₆^2*W.b₈*u^10 - 5799*W.b₆^2*u^14 - 72*W.b₆*W.b₈^3*u^5 - 2680*W.b₆*W.b₈^2*u^9 - 10104*W.b₆*W.b₈*u^13 - 1992*W.b₆*u^17 - 144*W.b₈^3*u^8 - 3408*W.b₈^2*u^12 - 2352*W.b₈*u^16 + 16*u^20) * hH

end MPP.Solutions.Bsd395
