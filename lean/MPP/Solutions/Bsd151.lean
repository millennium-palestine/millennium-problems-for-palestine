import Mathlib

namespace MPP.Solutions.Bsd151

open Finset

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    (2 : ℤ) ∣ (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)) -
      ((p : ℤ) - ((Finset.univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ)) := by
  intro p _ a b
  have hpt : ∀ y : ZMod p, (2 : ℤ) ∣ quadraticChar (ZMod p) y - (if y = 0 then 0 else 1) := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [if_neg hy]
      rcases quadraticChar_dichotomy hy with h | h <;> rw [h] <;> norm_num
  have hcard : ∀ x : ZMod p,
      (if x ^ 3 + a * x + b = 0 then (0 : ℤ) else 1) =
        1 - (if x ^ 3 + a * x + b = 0 then 1 else 0) := by
    intro x
    split_ifs <;> norm_num
  have hsum : ∑ x : ZMod p, (if x ^ 3 + a * x + b = 0 then (0 : ℤ) else 1) =
      (p : ℤ) - ((Finset.univ.filter fun x : ZMod p => x ^ 3 + a * x + b = 0).card : ℤ) := by
    simp only [hcard]
    rw [Finset.sum_sub_distrib, Finset.sum_boole]
    simp [ZMod.card]
  have h := Finset.dvd_sum (s := univ) (fun x _ => hpt (x ^ 3 + a * x + b))
  rw [Finset.sum_sub_distrib, hsum] at h
  exact h

end MPP.Solutions.Bsd151
