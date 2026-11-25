import Mathlib

namespace MPP.Solutions.Bsd156

theorem main : ∀ (p : ℕ) [Fact p.Prime] (e : ZMod p), p ≠ 2 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (-3 * e ^ 2) * x + 2 * e ^ 3)) ^ 2 ≤ 1 := by
  intro p _ e hp2
  have hring : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hpoly : ∀ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (-3 * e ^ 2) * x + 2 * e ^ 3)
      = quadraticChar (ZMod p) (x + 2 * e) - if x = e then quadraticChar (ZMod p) (3 * e) else 0 := by
    intro x
    have hf : x ^ 3 + (-3 * e ^ 2) * x + 2 * e ^ 3 = (x - e) ^ 2 * (x + 2 * e) := by ring
    rw [hf]
    by_cases hx : x = e
    · rw [if_pos hx, hx, show e + 2 * e = 3 * e by ring]
      simp
    · rw [if_neg hx, sub_zero, map_mul, quadraticChar_sq_one' (sub_ne_zero.mpr hx), one_mul]
  have hsum : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (-3 * e ^ 2) * x + 2 * e ^ 3)
      = -quadraticChar (ZMod p) (3 * e) := by
    rw [Finset.sum_congr rfl (fun x _ => hpoly x), Finset.sum_sub_distrib]
    have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) (x + 2 * e) = 0 :=
      (Equiv.sum_comp (Equiv.addRight (2 * e)) (fun x => quadraticChar (ZMod p) x)).trans
        (quadraticChar_sum_zero hring)
    have h2 : ∑ x : ZMod p, (if x = e then quadraticChar (ZMod p) (3 * e) else 0)
        = quadraticChar (ZMod p) (3 * e) := by
      simp
    rw [h1, h2, zero_sub]
  rw [hsum, neg_sq]
  by_cases h0 : 3 * e = 0
  · rw [h0, quadraticChar_zero]
    norm_num
  · exact (quadraticChar_sq_one h0).le

end MPP.Solutions.Bsd156
