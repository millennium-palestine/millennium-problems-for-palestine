import Mathlib

namespace MPP.Solutions.Bsd184

theorem main : ∀ (a s C : ℝ) (c : ℕ → ℝ), 0 < s → 0 ≤ C → |a| ≤ C * s → c 0 = 1 → c 1 = a →
    (∀ k : ℕ, c (k + 2) = a * c (k + 1) - s ^ 2 * c k) →
    ∀ k : ℕ, |c k| ≤ ((k : ℝ) + 1) * (C + 1) ^ k * s ^ k := by
  intro a s C c hs hC ha h0 h1 hrec
  have key : ∀ k : ℕ, |c k| ≤ ((k : ℝ) + 1) * (C + 1) ^ k * s ^ k ∧
      |c (k + 1)| ≤ ((k : ℝ) + 2) * (C + 1) ^ (k + 1) * s ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      constructor
      · simp [h0]
      · simp only [zero_add, h1, Nat.cast_zero, pow_one]
        nlinarith [mul_nonneg hC hs.le]
    | succ k ih =>
      have hc1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      have hc2 : ((k + 1 : ℕ) : ℝ) + 2 = (k : ℝ) + 3 := by push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [hc1]
        exact ih.2
      · show |c (k + 2)| ≤ (((k + 1 : ℕ) : ℝ) + 2) * (C + 1) ^ (k + 1 + 1) * s ^ (k + 1 + 1)
        rw [hc2, hrec k]
        have hpoly : (C : ℝ) * ((k : ℝ) + 2) * (C + 1) + ((k : ℝ) + 1) ≤
            ((k : ℝ) + 3) * (C + 1) ^ 2 := by
          nlinarith [mul_nonneg hC (Nat.cast_nonneg k : (0 : ℝ) ≤ k), sq_nonneg C,
            mul_nonneg (mul_nonneg hC (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) hC]
        have hp : (0 : ℝ) ≤ s ^ (k + 2) * (C + 1) ^ k := by positivity
        have hA : |a| * |c (k + 1)| ≤ (C * s) * (((k : ℝ) + 2) * (C + 1) ^ (k + 1) * s ^ (k + 1)) :=
          mul_le_mul ha ih.2 (abs_nonneg _) (mul_nonneg hC hs.le)
        have hB : s ^ 2 * |c k| ≤ s ^ 2 * (((k : ℝ) + 1) * (C + 1) ^ k * s ^ k) :=
          mul_le_mul_of_nonneg_left ih.1 (sq_nonneg s)
        have hsub : |a * c (k + 1) - s ^ 2 * c k| ≤ |a * c (k + 1)| + |s ^ 2 * c k| :=
          abs_sub _ _
        have habs1 : |a * c (k + 1)| = |a| * |c (k + 1)| := abs_mul _ _
        have habs2 : |s ^ 2 * c k| = s ^ 2 * |c k| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
        have hfin : (C * s) * (((k : ℝ) + 2) * (C + 1) ^ (k + 1) * s ^ (k + 1)) +
            s ^ 2 * (((k : ℝ) + 1) * (C + 1) ^ k * s ^ k) =
            s ^ (k + 2) * (C + 1) ^ k * (C * ((k : ℝ) + 2) * (C + 1) + ((k : ℝ) + 1)) := by
          ring
        have hfin2 : s ^ (k + 2) * (C + 1) ^ k * (C * ((k : ℝ) + 2) * (C + 1) + ((k : ℝ) + 1)) ≤
            s ^ (k + 2) * (C + 1) ^ k * (((k : ℝ) + 3) * (C + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hpoly hp
        have hfin3 : s ^ (k + 2) * (C + 1) ^ k * (((k : ℝ) + 3) * (C + 1) ^ 2) =
            ((k : ℝ) + 3) * (C + 1) ^ (k + 1 + 1) * s ^ (k + 1 + 1) := by
          ring
        linarith [hsub, habs1, habs2, hA, hB, hfin, hfin2, hfin3]
  exact fun k => (key k).1

end MPP.Solutions.Bsd184
