import Mathlib
import MPP.Solutions.Bsd214
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd226

namespace MPP.Solutions.Bsd222

/-! The n = 3 bracket identity for the division polynomials of a Weierstrass curve over a field.
Proved in the universal domain `MvPolynomial (Fin 3) ℤ`, where bsd-225 gives the nonvanishing of
`normEDS` and bsd-214 gives the n = 2 relations, by bsd-226; then transferred to `W.ψ` as in
`Bsd214.main`. -/

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K) (m : ℤ),
    W.ψ 4 * (W.ψ m * W.ψ (m + 1) * W.ψ (m - 1)) + W.ψ 2 ^ 3 * (W.ψ m * W.ψ (m - 2) * W.ψ (m + 2)) =
      W.ψ 2 * W.ψ 3 * (W.ψ (m - 1) ^ 2 * W.ψ (m + 2) + W.ψ (m - 2) * W.ψ (m + 1) ^ 2) := by
  intro K _ W m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hu := MPP.Solutions.Bsd226.main (MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
    (fun k hk => MPP.Solutions.Bsd225.main k hk)
    (fun n => MPP.Solutions.Bsd214.univ (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) hb n) m
  have hf := congrArg (MvPolynomial.aeval
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄] :
      MvPolynomial (Fin 3) ℤ →ₐ[ℤ] Polynomial (Polynomial K)) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  simp only [WeierstrassCurve.ψ, normEDS_two, normEDS_three, normEDS_four] at hf ⊢
  linear_combination hf

end MPP.Solutions.Bsd222
