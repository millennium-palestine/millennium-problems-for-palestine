import Mathlib

namespace MPP.Solutions.Bsd149

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a : ZMod p), p ≠ 2 → p % 4 = 3 →
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) = 0 := by
  intro p _ a hp2 h4
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
  have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) =
      -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) := by
    have hre := Equiv.sum_comp (Equiv.neg (ZMod p))
      (fun x : ZMod p => quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)))
    calc ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p))
        = ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + a * (-x) + (0 : ZMod p)) :=
          hre.symm
      _ = ∑ x : ZMod p, -quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) := by
          apply Finset.sum_congr rfl
          intro x _
          have hx : (-x) ^ 3 + a * (-x) + (0 : ZMod p) = (-1) * (x ^ 3 + a * x + (0 : ZMod p)) := by
            ring
          rw [hx, map_mul, hneg, neg_one_mul]
      _ = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + (0 : ZMod p)) :=
          Finset.sum_neg_distrib _
  linarith

end MPP.Solutions.Bsd149
