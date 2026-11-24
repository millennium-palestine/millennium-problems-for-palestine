import Mathlib

namespace MPP.Solutions.Bsd041

theorem main : ∀ q : ℚ, q ≠ 0 → ∃ d : ℤ, ∃ u : ℚ, Squarefree d.natAbs ∧ q = (d : ℚ) * u ^ 2 ∧
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → ((p : ℤ) ∣ q.num ∨ p ∣ q.den) := by
  intro q hq
  have hden0 : q.den ≠ 0 := q.den_nz
  set m : ℤ := q.num * (q.den : ℤ) with hm
  have hm0 : m ≠ 0 := mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast hden0)
  obtain ⟨a, b, hab, hasq⟩ := Nat.sq_mul_squarefree m.natAbs
  set d : ℤ := m.sign * a with hd
  have hs : m.sign.natAbs = 1 := by
    rcases lt_or_gt_of_ne hm0 with h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [Int.sign_eq_one_of_pos h]
  have hdabs : d.natAbs = a := by
    simp [hd, Int.natAbs_mul, hs]
  have hmd : m = d * (b : ℤ) ^ 2 := by
    have h2 : (m.natAbs : ℤ) = (b : ℤ) ^ 2 * a := by exact_mod_cast hab.symm
    calc m = m.sign * (m.natAbs : ℤ) := (Int.sign_mul_natAbs m).symm
      _ = d * (b : ℤ) ^ 2 := by rw [h2, hd]; ring
  have hmQ : (q.num : ℚ) * (q.den : ℚ) = (d : ℚ) * (b : ℚ) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hmd
    push_cast [hm] at this
    exact this
  have hdenQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast hden0
  refine ⟨d, (b : ℚ) / q.den, ?_, ?_, ?_⟩
  · rw [hdabs]
    exact hasq
  · have key : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
    rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hdenQ)]
    linear_combination (q.den : ℚ) * key + hmQ
  · intro p hp hpd
    have hpa : p ∣ d.natAbs := Int.ofNat_dvd_left.mp hpd
    rw [hdabs] at hpa
    have hpm : (p : ℤ) ∣ m := Int.ofNat_dvd_left.mpr (hpa.trans (hab ▸ dvd_mul_left a (b ^ 2)))
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpm with h | h
    · exact Or.inl h
    · exact Or.inr (Int.natCast_dvd_natCast.mp h)

end MPP.Solutions.Bsd041
