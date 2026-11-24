import Mathlib

namespace MPP.Solutions.Bsd017

theorem main : ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c → Int.gcd a b = 1 → a ^ 4 - b ^ 4 = c ^ 2 →
    Odd b → ∃ a' b' c' : ℤ, 0 < a' ∧ a' < a ∧ 0 < b' ∧ 0 < c' ∧ Int.gcd a' b' = 1 ∧
      a' ^ 4 - b' ^ 4 = c' ^ 2 := by
  intro a b c ha hb hc hab h hodd
  have hcopab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
  -- b² and c are coprime: c² = a⁴ − b⁴ and b is coprime to a
  have hb2c2 : IsCoprime (b ^ 2) (c ^ 2) := by
    obtain ⟨u, v, huv⟩ := (hcopab.symm.pow (m := 2) (n := 4))
    exact ⟨u + v * b ^ 2, v, by linear_combination huv - v * h⟩
  have hb2c : IsCoprime (b ^ 2) c := by
    have : IsCoprime (b ^ 2) (c * c) := by
      rw [← pow_two]
      exact hb2c2
    exact this.of_mul_right_left
  have hgcd : Int.gcd (b ^ 2) c = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb2c
  have hT : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
    unfold PythagoreanTriple
    linear_combination (-1 : ℤ) * h
  have hodd2 : (b ^ 2) % 2 = 1 := Int.odd_iff.mp (hodd.pow)
  obtain ⟨m, n, ⟨h1, h2, h3, h4, _, h6⟩⟩ :=
    PythagoreanTriple.coprime_classification' hT hgcd hodd2 (by positivity)
  have hm : 0 < m := by
    rcases h6.lt_or_eq with h7 | h7
    · exact h7
    · exfalso
      rw [← h7] at h2
      simp at h2
      omega
  have hn : 0 < n := by
    by_contra hn0
    have hn1 : n ≤ 0 := not_lt.mp hn0
    nlinarith
  have hlt : m < a := by
    by_contra hle
    have hle' : a ≤ m := not_lt.mp hle
    nlinarith
  refine ⟨m, n, a * b, hm, hlt, hn, mul_pos ha hb, h4, ?_⟩
  linear_combination (-(a ^ 2)) * h1 + (-(m ^ 2 - n ^ 2)) * h3

end MPP.Solutions.Bsd017
