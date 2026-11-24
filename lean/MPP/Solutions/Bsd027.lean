import Mathlib

namespace MPP.Solutions.Bsd027

theorem main : ∀ (G : Type) [AddCommGroup G] (h : G → ℝ) (C : ℝ),
    (∀ P : G, 0 ≤ h P) → (∀ P : G, h (-P) = h P) →
    (∀ P Q : G, h (P + Q) ≤ 2 * h P + 2 * h Q) →
    (∀ P : G, 4 * h P - C ≤ h (2 • P)) →
    (∀ M : ℝ, {P : G | h P ≤ M}.Finite) →
    (∃ s : Finset G, ∀ P : G, ∃ Q ∈ s, ∃ R : G, P = Q + 2 • R) →
    AddGroup.FG G := by
  intro G _ h C h0 hneg hadd hdbl hfin hrep
  obtain ⟨s, hs⟩ := hrep
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∑ Q ∈ s, h Q) + |C| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (Finset.sum_nonneg fun i _ => h0 i) (abs_nonneg C)
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * K + 2 := ⟨_, rfl⟩
  have key : ∀ n : ℕ, ∀ P : G, h P ≤ n →
      P ∈ AddSubgroup.closure ((s : Set G) ∪ {P : G | h P ≤ N}) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro P hP
      by_cases hsmall : h P ≤ N
      · exact AddSubgroup.subset_closure (Set.mem_union_right _ (show h P ≤ N from hsmall))
      · push_neg at hsmall
        obtain ⟨Q, hQ, R, rfl⟩ := hs P
        have e : 2 • R = (Q + 2 • R) + -Q := by abel
        have h2 : h (2 • R) ≤ 2 * h (Q + 2 • R) + 2 * h Q := by
          have := hadd (Q + 2 • R) (-Q)
          rw [hneg Q, ← e] at this
          exact this
        have hQle : h Q ≤ ∑ i ∈ s, h i := Finset.single_le_sum (fun i _ => h0 i) hQ
        have hRb : h R ≤ h (Q + 2 • R) / 2 + K := by
          rw [hK]
          linarith [hdbl R, le_abs_self C, abs_nonneg C, h0 Q]
        have hn1r : (1 : ℝ) ≤ n := by linarith
        have hn1 : 1 ≤ n := by exact_mod_cast hn1r
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub hn1, Nat.cast_one]
        have hRbound : h R ≤ ((n - 1 : ℕ) : ℝ) := by
          rw [hcast]
          linarith
        have hRT := ih (n - 1) (by omega) R hRbound
        exact AddSubgroup.add_mem _
          (AddSubgroup.subset_closure (Set.mem_union_left _ (Finset.mem_coe.mpr hQ)))
          (AddSubgroup.nsmul_mem _ hRT 2)
  have hS : ((s : Set G) ∪ {P : G | h P ≤ N}).Finite :=
    (Finset.finite_toSet s).union (hfin N)
  refine ⟨⟨hS.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, eq_top_iff]
  intro P _
  exact key ⌈h P⌉₊ P (Nat.le_ceil _)

end MPP.Solutions.Bsd027
