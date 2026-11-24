import Mathlib

namespace MPP.Solutions.Bsd053

theorem main : ∀ (e1 e2 e3 a1 a2 a3 : ℚ), e1 + e2 + e3 = 0 → a1 ^ 2 + e1 = a2 ^ 2 + e2 →
    a1 ^ 2 + e1 = a3 ^ 2 + e3 →
    (3 * (a1 ^ 2 + e1 + a1 * a2 + a2 * a3 + a3 * a1) ^ 2 + (e1 * e2 + e1 * e3 + e2 * e3)) ^ 2 =
      4 * ((a1 ^ 2 + e1 + a1 * a2 + a2 * a3 + a3 * a1) ^ 3 +
        (e1 * e2 + e1 * e3 + e2 * e3) * (a1 ^ 2 + e1 + a1 * a2 + a2 * a3 + a3 * a1) - e1 * e2 * e3) *
        (a1 ^ 2 + e1 + 2 * (a1 ^ 2 + e1 + a1 * a2 + a2 * a3 + a3 * a1)) := by
  intro e1 e2 e3 a1 a2 a3 hs h2 h3
  have he2 : e2 = a1 ^ 2 - a2 ^ 2 + e1 := by linarith
  have he3 : e3 = a1 ^ 2 - a3 ^ 2 + e1 := by linarith
  subst he2 he3
  have he1 : e1 = (a2 ^ 2 + a3 ^ 2 - 2 * a1 ^ 2) / 3 := by linarith
  subst he1
  ring

end MPP.Solutions.Bsd053
