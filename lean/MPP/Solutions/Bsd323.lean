import Mathlib
import MPP.Solutions.Bsd214

namespace MPP.Solutions.Bsd323

/-! The n = 2 elliptic-net relation for `normEDS` in an arbitrary commutative ring.
`MPP.Solutions.Bsd214.univ` gives it in a domain where `b ≠ 0`; here the universal
domain `MvPolynomial (Fin 3) ℤ` with `b = X 0` is used, and the identity is pushed
to `A` by the evaluation map at `![b, c, d]`. -/

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 2) * normEDS b c d (m - 2)
      - b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + c * normEDS b c d m ^ 2 = 0 := by
  intro A _ b c d m
  have hu := MPP.Solutions.Bsd214.univ (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X_ne_zero 0) m
  have hf := congrArg (MvPolynomial.aeval ![b, c, d] :
    MvPolynomial (Fin 3) ℤ →ₐ[ℤ] A) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  linear_combination hf

end MPP.Solutions.Bsd323
