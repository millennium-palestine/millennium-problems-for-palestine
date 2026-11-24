import Mathlib

namespace MPP.Solutions.Bsd023

theorem main : ∀ (c f : ℕ → ℝ), c 1 = 1 → f 1 = 1 →
    (∀ m n : ℕ, Nat.Coprime m n → c (m * n) = c m * c n) →
    (∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
    (∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k)) →
    (∀ p k : ℕ, p.Prime → |c (p ^ k)| ≤ f (p ^ k)) →
    ∀ n : ℕ, 0 < n → |c n| ≤ f n := by
  intro c f hc1 hf1 hcm hfm hfp hcb n hn
  -- strengthened claim: f is nonnegative and bounds |c| on every positive n
  have key : ∀ n : ℕ, 0 < n → 0 ≤ f n ∧ |c n| ≤ f n := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp _ => exact fun _ => ⟨hfp p k hp, hcb p k hp⟩
    | zero => intro h; exact absurd h (lt_irrefl 0)
    | one => intro _; rw [hc1, hf1]; norm_num
    | coprime a b ha hb hab iha ihb =>
      intro _
      obtain ⟨fa0, ca⟩ := iha (by omega)
      obtain ⟨fb0, cb⟩ := ihb (by omega)
      rw [hfm a b hab, hcm a b hab, abs_mul]
      exact ⟨mul_nonneg fa0 fb0, mul_le_mul ca cb (abs_nonneg _) fa0⟩
  exact (key n hn).2

end MPP.Solutions.Bsd023
