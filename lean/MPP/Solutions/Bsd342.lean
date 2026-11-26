import Mathlib

namespace MPP.Solutions.Bsd342

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    (∀ m n : ℤ, ¬ (p : ℤ) ∣ m → 0 ≤ m ^ 2 - ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) * m * n + (p : ℤ) * n ^ 2) →
      |((Nat.card W.toAffine.Point : ℕ) : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) := by
  intro p _ W _ h
  have key : ∀ (a q : ℤ), 1 < q → (∀ m n : ℤ, ¬ q ∣ m → 0 ≤ m ^ 2 - a * m * n + q * n ^ 2) → a ^ 2 ≤ 4 * q := by
    intro a q hq hq'
    by_cases hd : q ∣ a
    · obtain ⟨k, rfl⟩ := hd
      have hn : ¬ q ∣ (q * k + 1) := by
        intro h1
        have h2 : q ∣ 1 := by
          have := dvd_sub h1 (dvd_mul_right q k)
          simpa using this
        have := Int.le_of_dvd (by norm_num) h2
        omega
      have h2 := hq' (q * k + 1) 2 hn
      have h4 : q * k ^ 2 ≤ 4 := by
        by_contra hc
        have h5 : 4 + 1 ≤ q * k ^ 2 := Int.lt_iff_add_one_le.mp (not_le.mp hc)
        nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℤ) ≤ q by omega)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (show (0 : ℤ) ≤ q by omega)]
    · have h1 := hq' a 2 hd
      nlinarith [h1]
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hp1 : (1 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have ha := key ((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)) (p : ℤ) hp1 h
  have hx2 : ((p : ℝ) + 1 - ((Nat.card W.toAffine.Point : ℕ) : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast ha
  have habs := Real.abs_le_sqrt hx2
  have h4 : Real.sqrt (4 * (p : ℝ)) = 2 * Real.sqrt (p : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at habs
  rw [abs_sub_comm]
  exact habs

end MPP.Solutions.Bsd342
