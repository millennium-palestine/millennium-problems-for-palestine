import Mathlib

namespace MPP.Solutions.Bsd263

theorem main : ∀ (R : Type) [CommRing R] (K : ℕ) (G B : Polynomial R), B.natDegree < K →
    ∀ u : ℕ, K ≤ u →
      (G * B).coeff u = ∑ t ∈ Finset.range K, G.coeff (u - t) * B.coeff t := by
  intro R _ K G B hB u hu
  rw [Polynomial.coeff_mul]
  have h2 := Finset.Nat.sum_antidiagonal_swap (n := u)
    (f := fun x : ℕ × ℕ => G.coeff x.1 * B.coeff x.2)
  simp only [Prod.fst_swap, Prod.snd_swap] at h2
  rw [← h2, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => G.coeff j * B.coeff i) u]
  have hsub : Finset.range K ⊆ Finset.range (u + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [← Finset.sum_subset hsub]
  intro k _ hk
  rw [Finset.mem_range] at hk
  have hdeg : B.natDegree < k := by omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]

end MPP.Solutions.Bsd263
