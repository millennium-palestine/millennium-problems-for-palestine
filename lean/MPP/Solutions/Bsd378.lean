import Mathlib

namespace MPP.Solutions.Bsd378

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b : ZMod p,
    (Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1)).card
      + (Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1)).card
      + (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card = p := by
  intro p _ hp2 a b
  have hodd : p / 2 = (p - 1) / 2 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
    omega
  have hp3 : 2 < p := by
    have := (Fact.out : p.Prime).two_le
    omega
  haveI : Fact (2 < p) := ⟨hp3⟩
  have hk : (p - 1) / 2 ≠ 0 := by omega
  have hne : (1 : ZMod p) ≠ -1 := ZMod.neg_one_ne_one.symm
  have trichotomy : ∀ y : ZMod p,
      (if y ^ ((p - 1) / 2) = 1 then 1 else 0) + (if y ^ ((p - 1) / 2) = -1 then 1 else 0)
        + (if y = 0 then 1 else 0) = (1 : ℕ) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      rw [zero_pow hk]
      simp
    · rcases ZMod.pow_div_two_eq_neg_one_or_one p hy with h | h
      · rw [hodd] at h
        rw [h]
        simp [hne, hy]
      · rw [hodd] at h
        rw [h]
        simp [hne.symm, hy]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun x _ => trichotomy (x ^ 3 + a * x + b))]
  simp

end MPP.Solutions.Bsd378
