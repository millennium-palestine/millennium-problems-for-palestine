import Mathlib

namespace MPP.Solutions.Bsd326

theorem main : ∀ (a p : ℤ), 1 < p → (∀ m n : ℤ, ¬ p ∣ m → 0 ≤ m ^ 2 - a * m * n + p * n ^ 2) →
    ∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
  intro a p hp h
  have key : ∀ k : ℕ, ∀ m n : ℤ, m.natAbs + n.natAbs ≤ k →
      0 ≤ m ^ 2 - a * m * n + p * n ^ 2 := by
    intro k
    induction k with
    | zero =>
      intro m n hk
      have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst hm; subst hn; simp
    | succ k ih =>
      intro m n hk
      by_cases hm : p ∣ m
      · obtain ⟨m', rfl⟩ := hm
        by_cases hn : p ∣ n
        · obtain ⟨n', rfl⟩ := hn
          have hsmall : m'.natAbs + n'.natAbs ≤ k := by
            rw [Int.natAbs_mul, Int.natAbs_mul] at hk
            have h2 : 2 ≤ p.natAbs := by omega
            have h3 : 2 * (m'.natAbs + n'.natAbs) ≤ p.natAbs * m'.natAbs + p.natAbs * n'.natAbs := by
              nlinarith [Nat.zero_le m'.natAbs, Nat.zero_le n'.natAbs]
            omega
          have hih := ih m' n' hsmall
          have hform : (p * m') ^ 2 - a * (p * m') * (p * n') + p * (p * n') ^ 2 =
              p ^ 2 * (m' ^ 2 - a * m' * n' + p * n' ^ 2) := by ring
          rw [hform]
          have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
          exact mul_nonneg hp2 hih
        · have hn' := h n m' hn
          have hform : (p * m') ^ 2 - a * (p * m') * n + p * n ^ 2 =
              p * (n ^ 2 - a * n * m' + p * m' ^ 2) := by ring
          rw [hform]
          exact mul_nonneg (by linarith) hn'
      · exact h m n hm
  intro m n
  exact key _ m n le_rfl

end MPP.Solutions.Bsd326
