import Mathlib
import MPP.Solutions.Bsd155
import MPP.Solutions.Bsd156

namespace MPP.Solutions.Bsd157

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), p ≠ 2 → p ≠ 3 → 4 * a ^ 3 + 27 * b ^ 2 = 0 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b)) ^ 2 ≤ 4 * (p : ℤ) := by
  intro p hp a b hp2 hp3 h
  obtain ⟨e, rfl, rfl⟩ := MPP.Solutions.Bsd155.main p a b hp2 hp3 h
  have h1 := MPP.Solutions.Bsd156.main p e hp2
  have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.out.two_le
  linarith

end MPP.Solutions.Bsd157
