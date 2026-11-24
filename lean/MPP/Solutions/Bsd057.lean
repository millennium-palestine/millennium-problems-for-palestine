import Mathlib

namespace MPP.Solutions.Bsd057

theorem main : ∀ (a b c s : ℤ), Int.gcd a b = 1 → Int.gcd a c = 1 → Int.gcd b c = 1 → a * b * c = s ^ 2 →
    (∃ r : ℤ, a = r ^ 2 ∨ a = -r ^ 2) ∧ (∃ r : ℤ, b = r ^ 2 ∨ b = -r ^ 2) ∧
      (∃ r : ℤ, c = r ^ 2 ∨ c = -r ^ 2) := by
  intro a b c s hab hac hbc h
  have cab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
  have cac : IsCoprime a c := Int.isCoprime_iff_gcd_eq_one.mpr hac
  have cbc : IsCoprime b c := Int.isCoprime_iff_gcd_eq_one.mpr hbc
  have ha : IsCoprime a (b * c) := IsCoprime.mul_right cab cac
  have hb : IsCoprime b (a * c) := IsCoprime.mul_right cab.symm cbc
  have hc : IsCoprime c (a * b) := IsCoprime.mul_right cac.symm cbc.symm
  refine ⟨?_, ?_, ?_⟩
  · exact Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp ha) (by rw [← h]; ring)
  · exact Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hb) (by rw [← h]; ring)
  · exact Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hc) (by rw [← h]; ring)

end MPP.Solutions.Bsd057
