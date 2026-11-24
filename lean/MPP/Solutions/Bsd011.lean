import Mathlib
import MPP.Solutions.Bsd008

namespace MPP.Solutions.Bsd011

/-- If `N` is an integer and `q ≠ 0` is rational with `N = q²`, then `N = r²` for some integer
`r ≠ 0`. -/
theorem integer_root (N : ℤ) (q : ℚ) (h : (N : ℚ) = q * q) (hq : q ≠ 0) :
    ∃ r : ℤ, N = r * r ∧ r ≠ 0 := by
  obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.mp ⟨q, h⟩
  refine ⟨r, hr, ?_⟩
  rintro rfl
  apply hq
  have h0 : (N : ℚ) = 0 := by rw [hr]; simp
  rw [h0] at h
  exact mul_self_eq_zero.mp h.symm

theorem main : ∀ x y : ℚ, y ^ 2 = x ^ 3 - x → y ≠ 0 →
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2 := by
  intro x y hxy hy
  obtain ⟨u, hu⟩ := MPP.Solutions.Bsd008.main x y hxy
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hy
    have hx0 : x = 0 := by
      rcases hu with h | h <;> simpa using h
    have h2 : y ^ 2 = 0 := by rw [hxy, hx0]; ring
    exact (pow_eq_zero_iff (by norm_num)).mp h2
  have hnum : (u.num : ℚ) = u * (u.den : ℚ) := (Rat.mul_den_eq_num u).symm
  have hd0 : (u.den : ℤ) ≠ 0 := by exact_mod_cast u.den_nz
  have hn0 : u.num ≠ 0 := Rat.num_ne_zero.mpr hu0
  have hyu : y / u ≠ 0 := div_ne_zero hy hu0
  have hq0 : y / u * (u.den : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero hyu (pow_ne_zero 2 (by exact_mod_cast u.den_nz))
  rcases hu with hu | hu
  · -- case x = u²: (y/u)² = u⁴ − 1, so c² = a⁴ − b⁴ with a = u.num, b = u.den
    have e : y ^ 2 = u ^ 2 * (u ^ 4 - 1) := by rw [hxy, hu]; ring
    have e2 : (y / u) * (y / u) = u ^ 4 - 1 := by
      field_simp
      linear_combination e
    have hN : (((u.num ^ 4 - (u.den : ℤ) ^ 4 : ℤ)) : ℚ) =
        (y / u * (u.den : ℚ) ^ 2) * (y / u * (u.den : ℚ) ^ 2) := by
      push_cast
      rw [hnum]
      linear_combination (-((u.den : ℚ) ^ 4)) * e2
    obtain ⟨r, hr, hr0⟩ := integer_root _ _ hN hq0
    exact ⟨u.num, (u.den : ℤ), r, hn0, hd0, hr0, by rw [hr]; ring⟩
  · -- case x = −u²: (y/u)² = 1 − u⁴, so c² = b⁴ − a⁴; swap the roles of a and b
    have e : y ^ 2 = u ^ 2 * (1 - u ^ 4) := by rw [hxy, hu]; ring
    have e2 : (y / u) * (y / u) = 1 - u ^ 4 := by
      field_simp
      linear_combination e
    have hN : ((((u.den : ℤ) ^ 4 - u.num ^ 4 : ℤ)) : ℚ) =
        (y / u * (u.den : ℚ) ^ 2) * (y / u * (u.den : ℚ) ^ 2) := by
      push_cast
      rw [hnum]
      linear_combination (-((u.den : ℚ) ^ 4)) * e2
    obtain ⟨r, hr, hr0⟩ := integer_root _ _ hN hq0
    exact ⟨(u.den : ℤ), u.num, r, hd0, hn0, hr0, by rw [hr]; ring⟩

end MPP.Solutions.Bsd011
