import Mathlib

namespace MPP.Solutions.Bsd169

theorem main : ∀ (K : Type) [Field K] (g : Polynomial K) (J N : ℕ) (r : ℕ → Polynomial K),
    (∀ j < J, (r j).natDegree ≤ N) →
    (∑ j ∈ Finset.range J, r j * g ^ j).natDegree ≤ N + J * g.natDegree := by
  intro K _ g J N r hr
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : (r j * g ^ j).natDegree ≤ (r j).natDegree + (g ^ j).natDegree :=
    Polynomial.natDegree_mul_le
  have h2 : (g ^ j).natDegree ≤ j * g.natDegree := Polynomial.natDegree_pow_le
  have h3 : j * g.natDegree ≤ J * g.natDegree := Nat.mul_le_mul_right _ (le_of_lt hj)
  have h4 := hr j hj
  omega

end MPP.Solutions.Bsd169
