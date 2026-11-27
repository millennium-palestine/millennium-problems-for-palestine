import Mathlib

namespace MPP.Solutions.Bsd346

theorem main : ∀ (K : Type) [Field K] (W : WeierstrassCurve K),
    (∀ (k : ℤ),
      (∀ m : ℤ, W.ψ (m + k) * W.ψ (m - k) =
        W.ψ (m + 1) * W.ψ (m - 1) * W.ψ k ^ 2 - W.ψ (k + 1) * W.ψ (k - 1) * W.ψ m ^ 2) →
      (∀ m : ℤ, W.ψ (m + (k + 1)) * W.ψ (m - (k + 1)) =
        W.ψ (m + 1) * W.ψ (m - 1) * W.ψ (k + 1) ^ 2 - W.ψ (k + 1 + 1) * W.ψ (k + 1 - 1) * W.ψ m ^ 2) →
      ∀ m : ℤ, W.ψ (m + (k + 2)) * W.ψ (m - (k + 2)) =
        W.ψ (m + 1) * W.ψ (m - 1) * W.ψ (k + 2) ^ 2 - W.ψ (k + 2 + 1) * W.ψ (k + 2 - 1) * W.ψ m ^ 2) →
    (∀ m : ℤ, W.ψ (m + 0) * W.ψ (m - 0) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 0 ^ 2 - W.ψ (0 + 1) * W.ψ (0 - 1) * W.ψ m ^ 2) →
    (∀ m : ℤ, W.ψ (m + 1) * W.ψ (m - 1) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ 1 ^ 2 - W.ψ (1 + 1) * W.ψ (1 - 1) * W.ψ m ^ 2) →
    ∀ m n : ℤ, W.ψ (m + n) * W.ψ (m - n) =
      W.ψ (m + 1) * W.ψ (m - 1) * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1) * W.ψ m ^ 2 := by
  intro K _ W hs h0 h1
  -- the relation at index k
  let P : ℤ → Prop := fun k => ∀ m : ℤ, W.ψ (m + k) * W.ψ (m - k) =
    W.ψ (m + 1) * W.ψ (m - 1) * W.ψ k ^ 2 - W.ψ (k + 1) * W.ψ (k - 1) * W.ψ m ^ 2
  have step : ∀ k : ℤ, P k → P (k + 1) → P (k + 2) := fun k h2 h3 => hs k h2 h3
  have key : ∀ j : ℕ, P (j : ℤ) ∧ P ((j : ℤ) + 1) := by
    intro j
    induction j with
    | zero => simp only [Nat.cast_zero, zero_add]; exact ⟨h0, h1⟩
    | succ j ih =>
      have h4 := step _ ih.1 ih.2
      have e : (j : ℤ) + 1 + 1 = (j : ℤ) + 2 := by ring
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_succ]; exact ih.2
      · rw [Nat.cast_succ, e]; exact h4
  intro m n
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact (key k).1 m
  · have h5 := (key k).1 m
    have e1 : m + -(k : ℤ) = m - k := by ring
    have e2 : m - -(k : ℤ) = m + k := by ring
    have e3 : -(k : ℤ) + 1 = -((k : ℤ) - 1) := by ring
    have e4 : -(k : ℤ) - 1 = -((k : ℤ) + 1) := by ring
    rw [e1, e2, e3, e4]
    simp only [WeierstrassCurve.ψ_neg]
    linear_combination h5

end MPP.Solutions.Bsd346
