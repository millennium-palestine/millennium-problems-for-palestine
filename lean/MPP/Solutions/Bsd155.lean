import Mathlib

namespace MPP.Solutions.Bsd155

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), p ≠ 2 → p ≠ 3 → 4 * a ^ 3 + 27 * b ^ 2 = 0 →
    ∃ e : ZMod p, a = -3 * e ^ 2 ∧ b = 2 * e ^ 3 := by
  intro p _ a b hp2 hp3 h
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  have h27 : (27 : ZMod p) ≠ 0 := by
    have : (27 : ZMod p) = 3 ^ 3 := by norm_num
    rw [this]
    exact pow_ne_zero _ h3
  by_cases ha : a = 0
  · have hb2 : 27 * b ^ 2 = 0 := by
      rw [ha] at h
      linear_combination h
    have hb : b = 0 := by
      have : b ^ 2 = 0 := (mul_eq_zero.mp hb2).resolve_left h27
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    exact ⟨0, by rw [ha]; ring, by rw [hb]; ring⟩
  · have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
    set e : ZMod p := -3 * b / (2 * a) with he
    have hE : e * (2 * a) = -3 * b := div_mul_cancel₀ (-3 * b) h2a
    have hA : (2 * a) ^ 2 * (a + 3 * e ^ 2) = 0 := by
      linear_combination h + 3 * (e * (2 * a) - 3 * b) * hE
    have hB : (2 * a) ^ 3 * (b - 2 * e ^ 3) = 0 := by
      linear_combination 2 * b * h + (-2 * ((e * (2 * a)) ^ 2 + (e * (2 * a)) * (-3 * b) + 9 * b ^ 2)) * hE
    have hA' : a + 3 * e ^ 2 = 0 := (mul_eq_zero.mp hA).resolve_left (pow_ne_zero _ h2a)
    have hB' : b - 2 * e ^ 3 = 0 := (mul_eq_zero.mp hB).resolve_left (pow_ne_zero _ h2a)
    exact ⟨e, by linear_combination hA', by linear_combination hB'⟩

end MPP.Solutions.Bsd155
