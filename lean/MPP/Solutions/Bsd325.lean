import Mathlib
import MPP.Solutions.Bsd214
import MPP.Solutions.Bsd225
import MPP.Solutions.Bsd250
import MPP.Solutions.Bsd266
import MPP.Solutions.Bsd267
import MPP.Solutions.Bsd324

namespace MPP.Solutions.Bsd325

/-! The n = 4 elliptic-net relation `N(m+4) N(m-4) = N(4)^2 N(m+1) N(m-1) - N(5) N(3) N(m)^2`
for `normEDS`, in an arbitrary commutative ring.

First in a domain `R` where `b ≠ 0` and `normEDS` is nonzero off zero: the telescoping identity
of bsd-266 holds from the n = 2 and n = 3 relations (bsd-214 and bsd-324), the base case m = 2 is
bsd-267, and the induction principle of bsd-250 gives the relation for m ≥ 2. The case m ≤ -2 follows
from the symmetry of the bracket under m ↦ -m, and m ∈ {-1, 0, 1} is direct. The arbitrary ring case
is then the image of the universal domain `MvPolynomial (Fin 3) ℤ` under the evaluation at `![b, c, d]`. -/

section Gen

variable {R : Type} [CommRing R] [IsDomain R] (b c d : R)

lemma gen (hb : b ≠ 0) (hnv : ∀ k : ℤ, k ≠ 0 → normEDS b c d k ≠ 0) (m : ℤ) :
    normEDS b c d (m + 4) * normEDS b c d (m - 4)
      - normEDS b c d 4 ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d m ^ 2 = 0 := by
  have hY : ∀ s : ℤ, 2 ≤ s →
      normEDS b c d (s - 1) * normEDS b c d s * normEDS b c d (s + 1) ≠ 0 := by
    intro s hs
    exact mul_ne_zero (mul_ne_zero (hnv _ (by omega)) (hnv _ (by omega))) (hnv _ (by omega))
  have htel : ∀ s : ℤ, 2 ≤ s →
      normEDS b c d (s - 1) * normEDS b c d s * normEDS b c d (s + 1)
          * (normEDS b c d (s + 1 + 4) * normEDS b c d (s + 1 - 4)
            - normEDS b c d 4 ^ 2 * normEDS b c d (s + 1 + 1) * normEDS b c d (s + 1 - 1)
            + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d (s + 1) ^ 2)
        = normEDS b c d (s + 1 - 1) * normEDS b c d (s + 1) * normEDS b c d (s + 1 + 1)
          * (normEDS b c d (s + 4) * normEDS b c d (s - 4)
            - normEDS b c d 4 ^ 2 * normEDS b c d (s + 1) * normEDS b c d (s - 1)
            + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d s ^ 2) := by
    intro s _
    have h := MPP.Solutions.Bsd266.main R b c d s
      (fun k _ _ => MPP.Solutions.Bsd214.univ b c d hb k)
      (fun k _ _ => MPP.Solutions.Bsd324.main R b c d k)
    rw [show s + 1 - 1 = s by ring, show s + 1 + 1 = s + 2 by ring] at h ⊢
    exact h
  have hB2 : normEDS b c d (2 + 4) * normEDS b c d (2 - 4)
      - normEDS b c d 4 ^ 2 * normEDS b c d (2 + 1) * normEDS b c d (2 - 1)
      + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d 2 ^ 2 = 0 :=
    MPP.Solutions.Bsd267.main R b c d
  have key : ∀ s : ℤ, 2 ≤ s →
      normEDS b c d (s + 4) * normEDS b c d (s - 4)
        - normEDS b c d 4 ^ 2 * normEDS b c d (s + 1) * normEDS b c d (s - 1)
        + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d s ^ 2 = 0 :=
    MPP.Solutions.Bsd250.main R
      (fun s => normEDS b c d (s + 4) * normEDS b c d (s - 4)
        - normEDS b c d 4 ^ 2 * normEDS b c d (s + 1) * normEDS b c d (s - 1)
        + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d s ^ 2)
      (fun s => normEDS b c d (s - 1) * normEDS b c d s * normEDS b c d (s + 1))
      hY htel hB2
  rcases le_or_gt 2 m with hm | hm
  · exact key m hm
  rcases le_or_gt m (-2) with hm' | hm'
  · have h := key (-m) (by omega)
    rw [show -m + 4 = -(m - 4) by ring, show -m - 4 = -(m + 4) by ring,
      show -m + 1 = -(m - 1) by ring, show -m - 1 = -(m + 1) by ring] at h
    simp only [normEDS_neg] at h
    linear_combination h
  · interval_cases m <;> norm_num [normEDS_neg, normEDS_zero, normEDS_one] <;> ring

end Gen

theorem main : ∀ (A : Type) [CommRing A] (b c d : A) (m : ℤ),
    normEDS b c d (m + 4) * normEDS b c d (m - 4)
      - normEDS b c d 4 ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
      + normEDS b c d 5 * normEDS b c d 3 * normEDS b c d m ^ 2 = 0 := by
  intro A _ b c d m
  have hb : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) ≠ 0 := MvPolynomial.X_ne_zero 0
  have hu := gen (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1)
    (MvPolynomial.X 2) hb (fun k hk => MPP.Solutions.Bsd225.main k hk) m
  have hf := congrArg (MvPolynomial.aeval ![b, c, d] :
    MvPolynomial (Fin 3) ℤ →ₐ[ℤ] A) hu
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_normEDS,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hf
  linear_combination hf

end MPP.Solutions.Bsd325
