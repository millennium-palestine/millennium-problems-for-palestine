import Mathlib

namespace MPP.Solutions.Bsd019

theorem main : ∀ a b c : ℤ, Int.gcd a b = 1 → a ^ 4 - b ^ 4 = c ^ 2 →
    PythagoreanTriple c (b ^ 2) (a ^ 2) ∧ Int.gcd c (b ^ 2) = 1 := by
  intro a b c hab hyp
  refine ⟨?_, ?_⟩
  · unfold PythagoreanTriple
    linear_combination -hyp
  · have hc : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
    have h4 : IsCoprime (a ^ 4) (b ^ 4) := hc.pow
    obtain ⟨u, v, h'⟩ := h4
    -- substitute a^4 = c^2 + b^4 into the Bezout identity
    have e : u * c ^ 2 + (u + v) * b ^ 4 = 1 := by
      linear_combination h' - u * hyp
    have hcop : IsCoprime c (b ^ 2) := ⟨u * c, (u + v) * b ^ 2, by linear_combination e⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop

end MPP.Solutions.Bsd019
