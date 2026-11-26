import Mathlib

namespace MPP.Solutions.Bsd274

theorem disc_aux (p : ℕ) (a : ℤ)
    (h : ∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + (p : ℤ) * n ^ 2) : a ^ 2 ≤ 4 * (p : ℤ) := by
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

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    (∀ m n : ℤ, 0 ≤ m ^ 2 - ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) * m * n + (p : ℤ) * n ^ 2) →
    |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p _ W _ h
  have hdisc := disc_aux p _ h
  have hR : ((((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) : ℤ) : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast hdisc
  push_cast at hR
  have hs : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hsn : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

end MPP.Solutions.Bsd274
