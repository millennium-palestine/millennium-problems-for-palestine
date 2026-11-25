import Mathlib

namespace MPP.Solutions.Bsd167

theorem sum_degree_lt (K : Type) [Field K] (g : Polynomial K) (J : ℕ) (r : ℕ → Polynomial K)
    (hr : ∀ j < J, (r j).natDegree < g.natDegree) :
    (∑ j ∈ Finset.range J, r j * g ^ j).degree < ((J * g.natDegree : ℕ) : WithBot ℕ) := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (∑ j ∈ Finset.range n, r j * g ^ j).degree < ((n * g.natDegree : ℕ) : WithBot ℕ) :=
      ih (fun j hj => hr j (by omega))
    have h2 : (r n * g ^ n).degree < (((n + 1) * g.natDegree : ℕ) : WithBot ℕ) := by
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      have hnat : (r n * g ^ n).natDegree ≤ (r n).natDegree + n * g.natDegree := by
        calc (r n * g ^ n).natDegree ≤ (r n).natDegree + (g ^ n).natDegree :=
              Polynomial.natDegree_mul_le
          _ = (r n).natDegree + n * g.natDegree := by rw [Polynomial.natDegree_pow]
      have hlt : (r n).natDegree + n * g.natDegree < (n + 1) * g.natDegree := by
        have := hr n (by omega)
        nlinarith
      exact WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hnat hlt)
    have h3 : ((n * g.natDegree : ℕ) : WithBot ℕ) ≤ (((n + 1) * g.natDegree : ℕ) : WithBot ℕ) :=
      WithBot.coe_le_coe.mpr (Nat.mul_le_mul_right _ (Nat.le_succ n))
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (lt_of_lt_of_le h1 h3) h2)

theorem main : ∀ (K : Type) [Field K] (g : Polynomial K) (J : ℕ) (r : ℕ → Polynomial K), 0 < g.natDegree →
    (∀ j < J, (r j).natDegree < g.natDegree) →
    ∑ j ∈ Finset.range J, r j * g ^ j = 0 →
    ∀ j < J, r j = 0 := by
  intro K _ g J
  induction J with
  | zero => intro r _ _ j hj; omega
  | succ n ih =>
    intro r hd hr hsum
    rw [Finset.sum_range_succ] at hsum
    have hlow := sum_degree_lt K g n r (fun j hj => hr j (by omega))
    have hgne : g ^ n ≠ 0 := pow_ne_zero _ (fun h => by simp [h] at hd)
    have hrn : r n = 0 := by
      by_contra hne
      have hBdeg : (r n * g ^ n).degree = (((r n).natDegree + n * g.natDegree : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree (mul_ne_zero hne hgne),
          Polynomial.natDegree_mul hne hgne, Polynomial.natDegree_pow]
      have hlt : (∑ j ∈ Finset.range n, r j * g ^ j).degree < (r n * g ^ n).degree := by
        rw [hBdeg]
        exact lt_of_lt_of_le hlow (WithBot.coe_le_coe.mpr (Nat.le_add_left _ _))
      have hcontra := congrArg Polynomial.degree hsum
      rw [Polynomial.degree_add_eq_right_of_degree_lt hlt, Polynomial.degree_zero, hBdeg] at hcontra
      exact WithBot.coe_ne_bot hcontra
    rw [hrn, zero_mul, add_zero] at hsum
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact ih r hd (fun j hj => hr j (by omega)) hsum j h
    · rw [h]
      exact hrn

end MPP.Solutions.Bsd167
