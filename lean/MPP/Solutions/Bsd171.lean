import Mathlib

namespace MPP.Solutions.Bsd171

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ y : ZMod p,
    (y = 0 ∧ quadraticChar (ZMod p) y = 0) ∨
    (y ≠ 0 ∧ y ^ ((p - 1) / 2) = 1 ∧ quadraticChar (ZMod p) y = 1) ∨
    (y ≠ 0 ∧ y ^ ((p - 1) / 2) = -1 ∧ quadraticChar (ZMod p) y = -1) := by
  intro p _ hp2 y
  have hodd : (p - 1) / 2 = p / 2 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (Fact.out : p.Prime) hp2)
    omega
  by_cases hy : y = 0
  · exact Or.inl ⟨hy, by simp [hy]⟩
  · rw [hodd]
    by_cases hs : IsSquare y
    · have h1 : y ^ (p / 2) = 1 := (ZMod.euler_criterion p hy).mp hs
      exact Or.inr (Or.inl ⟨hy, h1, quadraticChar_one_iff_isSquare hy |>.mpr hs⟩)
    · have h1 : y ^ (p / 2) ≠ 1 := fun h => hs ((ZMod.euler_criterion p hy).mpr h)
      have h2 : y ^ (p / 2) = -1 := by
        rcases ZMod.pow_div_two_eq_neg_one_or_one p hy with h | h
        · exact absurd h h1
        · exact h
      exact Or.inr (Or.inr ⟨hy, h2, quadraticChar_neg_one_iff_not_isSquare.mpr hs⟩)

end MPP.Solutions.Bsd171
