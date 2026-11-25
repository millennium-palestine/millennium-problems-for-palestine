import Mathlib

namespace MPP.Solutions.Bsd147

theorem main : ∀ (p : ℕ) [Fact p.Prime] (b : ZMod p), p ≠ 2 → p % 3 ≠ 1 →
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b) = 0 := by
  intro p _ b hp2 h3
  have hp : p.Prime := Fact.out
  have h2p := hp.two_le
  have hcases : p = 3 ∨ p % 3 = 2 := by
    have h : p % 3 = 0 ∨ p % 3 = 2 := by omega
    rcases h with h | h
    · left
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
    · right
      exact h
  have hinj : Function.Injective (fun x : ZMod p => x ^ 3) := by
    rcases hcases with rfl | h2
    · intro x y hxy
      have hx : x ^ 3 = x := ZMod.pow_card x
      have hy : y ^ 3 = y := ZMod.pow_card y
      calc x = x ^ 3 := hx.symm
        _ = y ^ 3 := hxy
        _ = y := hy
    · have key : ∀ z : ZMod p, z ^ (2 * p - 1) = z := by
        intro z
        rcases eq_or_ne z 0 with rfl | hz
        · rw [zero_pow (by omega)]
        · have h := ZMod.pow_card_sub_one_eq_one hz
          rw [show 2 * p - 1 = (p - 1) * 2 + 1 by omega, pow_succ, pow_mul, h]
          simp
      obtain ⟨k, hk⟩ : ∃ k, 2 * p - 1 = 3 * k := ⟨(2 * p - 1) / 3, by omega⟩
      have hxk : ∀ z : ZMod p, (z ^ 3) ^ k = z := by
        intro z
        rw [← pow_mul, ← hk]
        exact key z
      intro x y hxy
      have hxy' : x ^ 3 = y ^ 3 := hxy
      calc x = (x ^ 3) ^ k := (hxk x).symm
        _ = (y ^ 3) ^ k := by rw [hxy']
        _ = y := hxk y
  let e : ZMod p ≃ ZMod p := Equiv.ofBijective (fun x : ZMod p => x ^ 3) (Finite.injective_iff_bijective.mp hinj)
  have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (0 : ZMod p) * x + b) =
      ∑ y : ZMod p, quadraticChar (ZMod p) (y + b) := by
    simp only [zero_mul, add_zero]
    exact Equiv.sum_comp e (fun y => quadraticChar (ZMod p) (y + b))
  have h2 : ∑ y : ZMod p, quadraticChar (ZMod p) (y + b) =
      ∑ z : ZMod p, quadraticChar (ZMod p) z :=
    Equiv.sum_comp (Equiv.addRight b) (fun z => quadraticChar (ZMod p) z)
  rw [h1, h2]
  exact quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2)

end MPP.Solutions.Bsd147
