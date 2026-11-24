import Mathlib

namespace MPP.Solutions.Bsd019

theorem main : ∀ a b c : ℤ, Int.gcd a b = 1 → a ^ 4 - b ^ 4 = c ^ 2 →
    PythagoreanTriple c (b ^ 2) (a ^ 2) ∧ Int.gcd c (b ^ 2) = 1 := by
  intro a b c hab h
  refine ⟨?_, ?_⟩
  · unfold PythagoreanTriple
    linear_combination (-1 : ℤ) * h
  · have hab' : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
    have h4 : IsCoprime (a ^ 4) (b ^ 2) := hab'.pow
    obtain ⟨u, v, huv⟩ := h4
    have hc2 : IsCoprime (c ^ 2) (b ^ 2) :=
      ⟨u, u * b ^ 2 + v, by linear_combination huv - u * h⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp ((IsCoprime.pow_left_iff (by norm_num)).mp hc2)

end MPP.Solutions.Bsd019
