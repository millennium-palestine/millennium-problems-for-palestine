import Mathlib
import MPP.Solutions.Bsd214
import MPP.Solutions.Bsd223
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd226

namespace MPP.Solutions.Bsd324

/-! The n = 3 elliptic-net relation for `normEDS` in an arbitrary commutative ring.
`MPP.Solutions.Bsd223.univ_T` gives it in a domain, from the nonvanishing of `normEDS`
off zero (bsd-225), the n = 2 relation (bsd-214) and the bsd-222 bracket (bsd-226).
Here it is applied in the universal domain `MvPolynomial (Fin 3) ℤ`, and the identity is
pushed to `A` by the evaluation map at `![b, c, d]`. -/

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 3) * normEDS b c d (m - 3)
      - c ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + normEDS b c d 4 * b * normEDS b c d m ^ 2 = 0 := by
  intro A _ b c d m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hnv := fun k (hk : k ≠ 0) => MPP.Solutions.Bsd225.main k hk
  have hR := fun n : ℤ => MPP.Solutions.Bsd214.univ (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) hb n
  have hu := MPP.Solutions.Bsd223.univ_T (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ)
    (MvPolynomial.X 1) (MvPolynomial.X 2) hnv hR
    (fun n => MPP.Solutions.Bsd226.main (MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 0)
      (MvPolynomial.X 1) (MvPolynomial.X 2) hnv hR n) m
  have hf := congrArg (MvPolynomial.aeval ![b, c, d] :
    MvPolynomial (Fin 3) ℤ →ₐ[ℤ] A) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  rw [normEDS_four]
  linear_combination hf

end MPP.Solutions.Bsd324
