import Mathlib

namespace MPP.Solutions.Bsd008

theorem main : ∀ x y : ℚ, y ^ 2 = x ^ 3 - x → ∃ u : ℚ, x = u ^ 2 ∨ x = -(u ^ 2) := by
  intro x y hxy
  have hx : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Rat.num_div_den]
  have hbpos : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    show Nat.gcd _ _ = 1
    simpa using x.reduced
  generalize x.num = a at hx hcop
  generalize hbdef : (x.den : ℤ) = b at hx hcop hbpos
  have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hbpos
  -- a * b * (a² − b²) is the square of the integer y * b² (after clearing denominators)
  have hsq : IsSquare ((a * b * (a ^ 2 - b ^ 2) : ℤ) : ℚ) := by
    refine ⟨y * (b : ℚ) ^ 2, ?_⟩
    have hb0 : (b : ℚ) ≠ 0 := ne_of_gt hbQ
    have e : y * (b : ℚ) ^ 2 * (y * (b : ℚ) ^ 2) = y ^ 2 * (b : ℚ) ^ 4 := by ring
    rw [e, hxy, hx]
    push_cast
    field_simp
  obtain ⟨c, hc⟩ := Rat.isSquare_intCast_iff.mp hsq
  -- pairwise coprimality
  have hb2 : IsCoprime b (a ^ 2 - b ^ 2) := by
    obtain ⟨u, v, huv⟩ := (hcop.symm.pow_right (n := 2))
    exact ⟨u + v * b, v, by linear_combination huv⟩
  have ha2 : IsCoprime a (a ^ 2 - b ^ 2) := by
    obtain ⟨p, q, hpq⟩ := (hcop.pow_right (n := 2))
    exact ⟨p + q * a, -q, by linear_combination hpq⟩
  have hab2 : IsCoprime b (a * (a ^ 2 - b ^ 2)) := hcop.symm.mul_right hb2
  have hab1 : IsCoprime a (b * (a ^ 2 - b ^ 2)) := hcop.mul_right ha2
  -- each of b and a is ± a square
  obtain ⟨t, ht⟩ := Int.sq_of_isCoprime hab2 (c := c) (by linear_combination hc)
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime hab1 (c := c) (by linear_combination hc)
  have hbt : b = t ^ 2 := by
    rcases ht with ht | ht
    · exact ht
    · exfalso
      nlinarith [sq_nonneg t]
  have ht0 : (t : ℚ) ≠ 0 := by
    intro h0
    have : (b : ℚ) = 0 := by
      rw [hbt]
      have : (t : ℚ) ^ 2 = 0 := by rw [h0]; ring
      exact_mod_cast this
    linarith
  have hbQt : (b : ℚ) = (t : ℚ) ^ 2 := by exact_mod_cast hbt
  rcases hs with hs | hs
  · refine ⟨(s : ℚ) / (t : ℚ), Or.inl ?_⟩
    have ha' : (a : ℚ) = (s : ℚ) ^ 2 := by exact_mod_cast hs
    rw [hx, ha', hbQt, div_pow]
  · refine ⟨(s : ℚ) / (t : ℚ), Or.inr ?_⟩
    have ha' : (a : ℚ) = -(s : ℚ) ^ 2 := by exact_mod_cast hs
    rw [hx, ha', hbQt, div_pow]
    ring

end MPP.Solutions.Bsd008
