import Mathlib

namespace MPP.Solutions.Bsd253

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (K : ℕ) (G B : Polynomial R),
    B.natDegree < K →
    (∀ i : Fin K, (G * B).coeff (K + (i : ℕ)) = 0) →
    (Matrix.of (fun (i t : Fin K) => G.coeff (K + (i : ℕ) - (t : ℕ)))).det ≠ 0 →
    B = 0 := by
  intro R _ _ K G B hdeg hcoef hdet
  have hsum : B = ∑ t ∈ Finset.range K, Polynomial.monomial t (B.coeff t) :=
    Polynomial.as_sum_range' B K hdeg
  have hrow : ∀ i : Fin K,
      Matrix.mulVec (Matrix.of (fun (i t : Fin K) => G.coeff (K + (i : ℕ) - (t : ℕ))))
        (fun t : Fin K => B.coeff (t : ℕ)) i = 0 := by
    intro i
    have h1 : (G * B).coeff (K + (i : ℕ)) =
        ∑ t ∈ Finset.range K, G.coeff (K + (i : ℕ) - t) * B.coeff t := by
      conv_lhs => rw [hsum]
      rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro t ht
      have htK : t < K := Finset.mem_range.mp ht
      rw [show K + (i : ℕ) = (K + (i : ℕ) - t) + t by omega, Polynomial.coeff_mul_monomial,
        Nat.add_sub_cancel]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun t => G.coeff (K + (i : ℕ) - t) * B.coeff t) K, ← h1,
      hcoef i]
  have hzero : (fun t : Fin K => B.coeff (t : ℕ)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet (funext hrow)
  ext n
  by_cases hn : n < K
  · simpa using congrFun hzero ⟨n, hn⟩
  · rw [Polynomial.coeff_zero, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hdeg (not_lt.mp hn))]

end MPP.Solutions.Bsd253
