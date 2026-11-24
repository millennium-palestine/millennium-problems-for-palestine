import Mathlib

namespace MPP.Solutions.Bsd048

theorem main : ∀ (N M : ℤ) (u : ℚ), M ≠ 0 → u = (N : ℚ) / (M : ℚ) →
    max (u.num.natAbs : ℕ) u.den ≤ max N.natAbs M.natAbs := by
  intro N M u hM hu
  have hcop : IsCoprime u.num (u.den : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using u.reduced)
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have hu' : u * (M : ℚ) = N := by
    rw [hu]
    field_simp
  have hZ : u.num * M = N * (u.den : ℤ) := by
    have hQ : (u.num : ℚ) * (M : ℚ) = (N : ℚ) * (u.den : ℚ) := by
      rw [← Rat.mul_den_eq_num]
      linear_combination (u.den : ℚ) * hu'
    exact_mod_cast hQ
  have hdenM : (u.den : ℤ) ∣ M := by
    have h1 : (u.den : ℤ) ∣ M * u.num := ⟨N, by linear_combination hZ⟩
    exact hcop.symm.dvd_of_dvd_mul_right h1
  have hnumN : u.num.natAbs ≤ N.natAbs := by
    rcases eq_or_ne N 0 with hN | hN
    · subst hN
      have h0 : u.num = 0 := by simpa [hM] using hZ
      simp [h0]
    · have h2 : u.num ∣ N * (u.den : ℤ) := ⟨M, by linear_combination -hZ⟩
      have h3 : u.num ∣ N := hcop.dvd_of_dvd_mul_right h2
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hN) (Int.natAbs_dvd_natAbs.mpr h3)
  have hdenM' : u.den ≤ M.natAbs := by
    have h4 : (u.den : ℤ).natAbs ∣ M.natAbs := Int.natAbs_dvd_natAbs.mpr hdenM
    have h5 := Nat.le_of_dvd (Int.natAbs_pos.mpr hM) h4
    simpa using h5
  exact max_le (hnumN.trans (le_max_left _ _)) (hdenM'.trans (le_max_right _ _))

end MPP.Solutions.Bsd048
