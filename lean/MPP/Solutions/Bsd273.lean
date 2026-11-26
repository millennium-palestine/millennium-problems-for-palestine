import Mathlib

namespace MPP.Solutions.Bsd273

theorem main : ∀ (p : ℕ) (a : ℤ), 0 < p →
    (∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + (p : ℤ) * n ^ 2) →
    a ^ 2 ≤ 4 * (p : ℤ) := by
  intro p a hp h
  by_contra hcon
  have hcon' : 4 * (p : ℤ) < a ^ 2 := not_le.mp hcon
  have hcomp : 4 * (p : ℝ) < (a : ℝ) ^ 2 := by exact_mod_cast hcon'
  have hDpos : (0 : ℝ) < (a : ℝ) ^ 2 - 4 * (p : ℝ) := by linarith
  have hs : Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ)) ^ 2 = (a : ℝ) ^ 2 - 4 * (p : ℝ) :=
    Real.sq_sqrt hDpos.le
  have hsp : 0 < Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ)) := Real.sqrt_pos.mpr hDpos
  have htlt : ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ))) / 2 <
      ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ))) / 2 := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htlt
  have hprod : 0 < ((q : ℝ) - ((a : ℝ) - Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ))) / 2) *
      (((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ))) / 2 - (q : ℝ)) := by
    apply mul_pos <;> linarith
  have key : (q : ℝ) ^ 2 - (a : ℝ) * (q : ℝ) + (p : ℝ) < 0 := by
    nlinarith [hprod, hs]
  have hnum : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
    rw [Rat.cast_def]
    field_simp
  have h0 := h q.num (q.den : ℤ)
  have h1 : (0 : ℝ) ≤ (q.num : ℝ) ^ 2 - (a : ℝ) * (q.num : ℝ) * (q.den : ℝ) +
      (p : ℝ) * (q.den : ℝ) ^ 2 := by
    exact_mod_cast h0
  have e : (q.num : ℝ) ^ 2 - (a : ℝ) * (q.num : ℝ) * (q.den : ℝ) +
      (p : ℝ) * (q.den : ℝ) ^ 2 = (q.den : ℝ) ^ 2 * ((q : ℝ) ^ 2 - (a : ℝ) * (q : ℝ) + (p : ℝ)) := by
    rw [hnum]
    ring
  have hneg : (q.den : ℝ) ^ 2 * ((q : ℝ) ^ 2 - (a : ℝ) * (q : ℝ) + (p : ℝ)) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) key
  linarith [h1, e, hneg]

end MPP.Solutions.Bsd273
