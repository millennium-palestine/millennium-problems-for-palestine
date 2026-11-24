import Mathlib

namespace MPP.Solutions.Bsd047

theorem main : ∀ (A B C : ℤ) (u : ℚ), A ≠ 0 → (A : ℚ) * u ^ 2 + (B : ℚ) * u + (C : ℚ) = 0 →
    u.num.natAbs ≤ max A.natAbs (max B.natAbs C.natAbs) ∧ u.den ≤ A.natAbs := by
  intro A B C u hA h
  have hcop : IsCoprime u.num (u.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using u.reduced)
  have hkey : A * u.num ^ 2 + B * u.num * (u.den : ℤ) + C * (u.den : ℤ) ^ 2 = 0 := by
    have hQ : (A : ℚ) * (u.num : ℚ) ^ 2 + (B : ℚ) * (u.num : ℚ) * (u.den : ℚ)
        + (C : ℚ) * (u.den : ℚ) ^ 2 = 0 := by
      rw [← Rat.mul_den_eq_num]
      linear_combination (u.den : ℚ) ^ 2 * h
    exact_mod_cast hQ
  have hdenA : (u.den : ℤ) ∣ A := by
    have h1 : (u.den : ℤ) ∣ A * u.num ^ 2 :=
      ⟨-(B * u.num + C * (u.den : ℤ)), by linear_combination hkey⟩
    exact (IsCoprime.pow_right hcop.symm).dvd_of_dvd_mul_right h1
  have hden : u.den ≤ A.natAbs := by
    have h2 : (u.den : ℤ).natAbs ∣ A.natAbs := Int.natAbs_dvd_natAbs.mpr hdenA
    simpa using Nat.le_of_dvd (Int.natAbs_pos.mpr hA) h2
  refine ⟨?_, hden⟩
  rcases eq_or_ne u.num 0 with hp | hp
  · simp [hp]
  by_cases hC : C = 0
  · subst hC
    have hlin : A * u.num + B * (u.den : ℤ) = 0 := by
      have : u.num * (A * u.num + B * (u.den : ℤ)) = 0 := by linear_combination hkey
      exact (mul_eq_zero.mp this).resolve_left hp
    have hB : B ≠ 0 := by
      rintro rfl
      have : A * u.num = 0 := by simpa using hlin
      exact hp ((mul_eq_zero.mp this).resolve_left hA)
    have h3 : u.num ∣ B * (u.den : ℤ) := ⟨-A, by linear_combination hlin⟩
    have h5 : u.num ∣ B := hcop.dvd_of_dvd_mul_right h3
    have h7 : u.num.natAbs ≤ B.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hB) (Int.natAbs_dvd_natAbs.mpr h5)
    exact h7.trans (le_max_of_le_right (le_max_of_le_left le_rfl))
  · have h4 : u.num ∣ C * (u.den : ℤ) ^ 2 :=
      ⟨-(A * u.num + B * (u.den : ℤ)), by linear_combination hkey⟩
    have h5 : u.num ∣ C := (IsCoprime.pow_right hcop).dvd_of_dvd_mul_right h4
    have h7 : u.num.natAbs ≤ C.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hC) (Int.natAbs_dvd_natAbs.mpr h5)
    exact h7.trans (le_max_of_le_right (le_max_of_le_right le_rfl))

end MPP.Solutions.Bsd047
