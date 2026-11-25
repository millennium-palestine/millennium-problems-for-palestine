import Mathlib
import MPP.Solutions.Bsd214
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd226

namespace MPP.Solutions.Bsd223

/-! The n = 3 instance of the elliptic-net addition formula `N(m+3) N(m-3) = N(m+1) N(m-1) N(3)^2 - N(4) N(2) N(m)^2`.
In a domain, the bsd-222 bracket (bsd-226) and the n = 2 relations (bsd-214) give
`N(m+1) N(m-1) T(m) = b N(m) B(m) + (cofactors) * R`, so `T(m) = 0` wherever `N(m+1) N(m-1) ≠ 0`, which is
every `m` outside `{-1, 0, 1}` by nonvanishing (bsd-225). The three exceptional indices are direct. -/

section Universal

variable {A : Type*} [CommRing A] [IsDomain A] (b c d : A)

lemma univ_T
    (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0)
    (hR : ∀ m : ℤ, normEDS b c d (m + 2) * normEDS b c d (m - 2)
      - b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1) + c * normEDS b c d m ^ 2 = 0)
    (hB : ∀ m : ℤ, normEDS b c d 4 * (normEDS b c d m * normEDS b c d (m + 1) * normEDS b c d (m - 1))
      + b ^ 3 * (normEDS b c d m * normEDS b c d (m - 2) * normEDS b c d (m + 2))
      - b * c * (normEDS b c d (m - 1) ^ 2 * normEDS b c d (m + 2)
        + normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2) = 0)
    (m : ℤ) :
    normEDS b c d (m + 3) * normEDS b c d (m - 3) - c ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + d * b ^ 2 * normEDS b c d m ^ 2 = 0 := by
  have hB' : normEDS b c d (m + 1) * normEDS b c d (m - 1) *
      (normEDS b c d (m + 3) * normEDS b c d (m - 3) - c ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        + d * b ^ 2 * normEDS b c d m ^ 2) = 0 := by
    have hBm := hB m
    have hR1 := hR (m - 1)
    have hR3 := hR (m + 1)
    simp only [show m - 1 + 2 = m + 1 by ring, show m - 1 - 2 = m - 3 by ring,
      show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring] at hR1
    simp only [show m + 1 + 2 = m + 3 by ring, show m + 1 - 2 = m - 1 by ring,
      show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at hR3
    rw [normEDS_four] at hBm
    linear_combination (b * normEDS b c d m) * hBm
      + (b ^ 2 * normEDS b c d m * normEDS b c d (m + 2) - c * normEDS b c d (m + 1) ^ 2) * hR1
      + (normEDS b c d (m + 1) * normEDS b c d (m - 3)) * hR3
  rcases eq_or_ne m 0 with h0 | h0
  · subst h0
    simp [normEDS_neg, normEDS_zero, normEDS_one, normEDS_three]
    ring
  rcases eq_or_ne m 1 with h1 | h1
  · subst h1
    simp [normEDS_neg, normEDS_zero, normEDS_two, normEDS_four]
    ring
  rcases eq_or_ne m (-1) with h2 | h2
  · subst h2
    simp [normEDS_neg, normEDS_zero, normEDS_two, normEDS_four]
    ring
  have hp : normEDS b c d (m + 1) ≠ 0 := hnv _ (by omega)
  have hq : normEDS b c d (m - 1) ≠ 0 := hnv _ (by omega)
  exact (mul_eq_zero.mp hB').resolve_left (mul_ne_zero hp hq)

end Universal

/-- The n = 3 instance of the elliptic-net addition formula for the division polynomials. -/
theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (m : ℤ),
    W.ψ (m + 3) * W.ψ (m - 3) = W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 3 ^ 2 - W.ψ 4 * W.ψ 2 * W.ψ m ^ 2 := by
  intro K _ W m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hR := fun n : ℤ => MPP.Solutions.Bsd214.univ (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) hb n
  have hu := univ_T (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1) (MvPolynomial.X 2)
    (fun k hk => MPP.Solutions.Bsd225.main k hk) hR
    (fun n => MPP.Solutions.Bsd226.main (MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 0)
      (MvPolynomial.X 1) (MvPolynomial.X 2) (fun k hk => MPP.Solutions.Bsd225.main k hk) hR n) m
  have hf := congrArg (MvPolynomial.aeval
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄] :
      MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial K)) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  simp only [WeierstrassCurve.ψ, normEDS_two, normEDS_three, normEDS_four] at hf ⊢
  linear_combination hf

end MPP.Solutions.Bsd223
