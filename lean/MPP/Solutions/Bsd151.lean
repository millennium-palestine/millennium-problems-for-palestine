import Mathlib

namespace MPP.Solutions.Bsd151

open Finset

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    (2 : ℤ) ∣ (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)) -
      ((p : ℤ) - ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)) := by
  intro p _ a b
  have key : ∀ y : ZMod p,
      (2 : ℤ) ∣ quadraticChar (ZMod p) y - (if y = 0 then 0 else 1) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp
    · rcases quadraticChar_dichotomy hy with h | h <;> simp [hy, h]
  have hle : (univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card ≤ p := by
    simpa [ZMod.card] using card_le_univ (univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0)
  have hcount : (p : ℤ) - ((univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)
      = ∑ x : ZMod p, (if x ^ 3 + a * x + b = 0 then (0 : ℤ) else 1) := by
    rw [Finset.sum_ite]
    simp [Finset.filter_not, Finset.card_univ_sdiff, ZMod.card, Nat.cast_sub hle]
  rw [hcount, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun x _ => key _

end MPP.Solutions.Bsd151
