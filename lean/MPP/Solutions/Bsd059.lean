import Mathlib

namespace MPP.Solutions.Bsd059

theorem main : ∀ (p q : ℤ) (x y : ℚ), y ^ 2 = x ^ 3 + (p : ℚ) * x + (q : ℚ) → ∃ r : ℕ, x.den = r ^ 2 := by
  intro p q x y h
  have hb0 : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have hd0 : (y.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr y.den_nz
  have hx : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hy : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
  -- the equation, cleared of denominators, in ℤ
  have key : (y.num : ℤ) ^ 2 * (x.den : ℤ) ^ 3 =
      (y.den : ℤ) ^ 2 * (x.num ^ 3 + p * x.num * (x.den : ℤ) ^ 2 + q * (x.den : ℤ) ^ 3) := by
    have h2 : ((y.num : ℚ)) ^ 2 * (x.den : ℚ) ^ 3 =
        (y.den : ℚ) ^ 2 * ((x.num : ℚ) ^ 3 + (p : ℚ) * x.num * (x.den : ℚ) ^ 2 + (q : ℚ) * (x.den : ℚ) ^ 3) := by
      rw [hx, hy] at h
      field_simp at h
      linear_combination h
    exact_mod_cast h2
  have cxy : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime] using x.reduced
  have cyy : IsCoprime y.num (y.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime] using y.reduced
  -- N = a³ + pab² + qb³ is prime to b
  have hN : IsCoprime (x.num ^ 3 + p * x.num * (x.den : ℤ) ^ 2 + q * (x.den : ℤ) ^ 3) (x.den : ℤ) := by
    have h3 : IsCoprime (x.num ^ 3) (x.den : ℤ) := cxy.pow_left
    have e : x.num ^ 3 + p * x.num * (x.den : ℤ) ^ 2 + q * (x.den : ℤ) ^ 3 =
        x.num ^ 3 + (x.den : ℤ) * (p * x.num * (x.den : ℤ) + q * (x.den : ℤ) ^ 2) := by ring
    rw [e]
    exact h3.add_mul_left_left _
  have hb3 : (x.den : ℤ) ^ 3 ∣ (y.den : ℤ) ^ 2 := by
    have hdiv : (x.den : ℤ) ^ 3 ∣ (y.den : ℤ) ^ 2 *
        (x.num ^ 3 + p * x.num * (x.den : ℤ) ^ 2 + q * (x.den : ℤ) ^ 3) :=
      ⟨(y.num : ℤ) ^ 2, by rw [← key]; ring⟩
    exact (hN.symm.pow_left).dvd_of_dvd_mul_right hdiv
  have hd2 : (y.den : ℤ) ^ 2 ∣ (x.den : ℤ) ^ 3 := by
    have hdiv : (y.den : ℤ) ^ 2 ∣ (y.num : ℤ) ^ 2 * (x.den : ℤ) ^ 3 := ⟨_, key⟩
    have cdd : IsCoprime ((y.den : ℤ) ^ 2) ((y.num : ℤ) ^ 2) := cyy.symm.pow
    exact cdd.dvd_of_dvd_mul_left hdiv
  have heq : (x.den : ℤ) ^ 3 = (y.den : ℤ) ^ 2 :=
    Int.dvd_antisymm (pow_nonneg (Int.natCast_nonneg _) 3) (pow_nonneg (Int.natCast_nonneg _) 2) hb3 hd2
  have heqQ : (x.den : ℚ) ^ 3 = (y.den : ℚ) ^ 2 := by exact_mod_cast heq
  have hsq : IsSquare (x.den : ℚ) := by
    refine ⟨(y.den : ℚ) / (x.den : ℚ), ?_⟩
    field_simp
    linear_combination heqQ
  obtain ⟨r, hr⟩ := Rat.isSquare_natCast_iff.mp hsq
  exact ⟨r, by rw [hr]; ring⟩

end MPP.Solutions.Bsd059
