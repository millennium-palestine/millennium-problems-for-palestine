import Mathlib

namespace MPP.Solutions.Bsd376

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b : ZMod p,
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) =
      ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = 1)).card : ℤ)
        - ((Finset.univ.filter (fun x : ZMod p => (x ^ 3 + a * x + b) ^ ((p - 1) / 2) = -1)).card : ℤ) := by
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
  have key : ∀ y : ZMod p, quadraticChar (ZMod p) y =
      (if y ^ ((p - 1) / 2) = 1 then 1 else 0) - (if y ^ ((p - 1) / 2) = -1 then 1 else 0) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      rw [zero_pow hk]
      simp
    · rcases ZMod.pow_div_two_eq_neg_one_or_one p hy with h | h
      · rw [hodd] at h
        have hq : quadraticChar (ZMod p) y = 1 :=
          (quadraticChar_one_iff_isSquare hy).2 ((ZMod.euler_criterion p hy).2 (by rw [hodd]; exact h))
        rw [hq, h]
        simp [hne]
      · rw [hodd] at h
        have hq : quadraticChar (ZMod p) y = -1 := by
          refine quadraticChar_neg_one_iff_not_isSquare.2 (fun hs => ?_)
          have h1 := (ZMod.euler_criterion p hy).1 hs
          rw [hodd] at h1
          rw [h1] at h
          exact hne h
        rw [hq, h]
        simp [hne.symm]
  rw [Finset.sum_congr rfl (fun x _ => key _), Finset.sum_sub_distrib]
  simp [Finset.sum_boole]

end MPP.Solutions.Bsd376
