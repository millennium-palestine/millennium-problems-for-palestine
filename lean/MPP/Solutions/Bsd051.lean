import Mathlib

namespace MPP.Solutions.Bsd051

-- quotient height (as in bsd-048)
theorem quot_height : ∀ (N M : ℤ) (u : ℚ), M ≠ 0 → u = (N : ℚ) / (M : ℚ) →
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

-- clearing denominators
theorem clr (b : ℚ) (c : ℕ) (hc : b.den ∣ c) : ∃ z : ℤ, (c : ℚ) * b = z := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨k * b.num, ?_⟩
  rw [hk]
  push_cast
  linear_combination (k : ℚ) * Rat.mul_den_eq_num b

-- coefficient bounds for the two integer forms
theorem bnd_F (a d H c z4 z6 z8 : ℤ) (ha : |a| ≤ H) (hd : |d| ≤ H) :
    |c * a ^ 4 - z4 * a ^ 2 * d ^ 2 - 2 * z6 * a * d ^ 3 - z8 * d ^ 4|
      ≤ (|c| + |z4| + 2 * |z6| + |z8|) * H ^ 4 := by
  have hH : 0 ≤ H := le_trans (abs_nonneg a) ha
  have h1 : |a| ^ 4 ≤ H ^ 4 := by gcongr
  have h2 : |a| ^ 2 * |d| ^ 2 ≤ H ^ 4 := by
    have : |a| ^ 2 ≤ H ^ 2 := by gcongr
    have : |d| ^ 2 ≤ H ^ 2 := by gcongr
    calc |a| ^ 2 * |d| ^ 2 ≤ H ^ 2 * H ^ 2 := by gcongr
      _ = H ^ 4 := by ring
  have h3 : |a| * |d| ^ 3 ≤ H ^ 4 := by
    have : |d| ^ 3 ≤ H ^ 3 := by gcongr
    calc |a| * |d| ^ 3 ≤ H * H ^ 3 := by gcongr
      _ = H ^ 4 := by ring
  have h4 : |d| ^ 4 ≤ H ^ 4 := by gcongr
  have e1 : |c * a ^ 4| ≤ |c| * H ^ 4 := by
    rw [abs_mul, abs_pow]
    gcongr
  have e2 : |z4 * a ^ 2 * d ^ 2| ≤ |z4| * H ^ 4 := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    calc |z4| * |a| ^ 2 * |d| ^ 2 = |z4| * (|a| ^ 2 * |d| ^ 2) := by ring
      _ ≤ |z4| * H ^ 4 := by gcongr
  have e3 : |2 * z6 * a * d ^ 3| ≤ 2 * |z6| * H ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow]
    have : |(2 : ℤ)| = 2 := by norm_num
    rw [this]
    calc 2 * |z6| * |a| * |d| ^ 3 = 2 * |z6| * (|a| * |d| ^ 3) := by ring
      _ ≤ 2 * |z6| * H ^ 4 := by gcongr
  have e4 : |z8 * d ^ 4| ≤ |z8| * H ^ 4 := by
    rw [abs_mul, abs_pow]
    gcongr
  calc |c * a ^ 4 - z4 * a ^ 2 * d ^ 2 - 2 * z6 * a * d ^ 3 - z8 * d ^ 4|
      ≤ |c * a ^ 4 - z4 * a ^ 2 * d ^ 2 - 2 * z6 * a * d ^ 3| + |z8 * d ^ 4| := abs_sub _ _
    _ ≤ |c * a ^ 4 - z4 * a ^ 2 * d ^ 2| + |2 * z6 * a * d ^ 3| + |z8 * d ^ 4| := by
        gcongr
        exact abs_sub _ _
    _ ≤ |c * a ^ 4| + |z4 * a ^ 2 * d ^ 2| + |2 * z6 * a * d ^ 3| + |z8 * d ^ 4| := by
        gcongr
        exact abs_sub _ _
    _ ≤ |c| * H ^ 4 + |z4| * H ^ 4 + 2 * |z6| * H ^ 4 + |z8| * H ^ 4 := by
        gcongr
    _ = (|c| + |z4| + 2 * |z6| + |z8|) * H ^ 4 := by ring


theorem bnd_G (a d H c z2 z4 z6 : ℤ) (ha : |a| ≤ H) (hd : |d| ≤ H) :
    |4 * c * a ^ 3 + z2 * a ^ 2 * d + 2 * z4 * a * d ^ 2 + z6 * d ^ 3|
      ≤ (4 * |c| + |z2| + 2 * |z4| + |z6|) * H ^ 3 := by
  have hH : 0 ≤ H := le_trans (abs_nonneg a) ha
  have e1 : |4 * c * a ^ 3| ≤ 4 * |c| * H ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow]
    have : |(4 : ℤ)| = 4 := by norm_num
    rw [this]
    gcongr
  have e2 : |z2 * a ^ 2 * d| ≤ |z2| * H ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow]
    calc |z2| * |a| ^ 2 * |d| = |z2| * (|a| ^ 2 * |d|) := by ring
      _ ≤ |z2| * H ^ 3 := by
        have : |a| ^ 2 * |d| ≤ H ^ 2 * H := by gcongr
        calc |z2| * (|a| ^ 2 * |d|) ≤ |z2| * (H ^ 2 * H) := by gcongr
          _ = |z2| * H ^ 3 := by ring
  have e3 : |2 * z4 * a * d ^ 2| ≤ 2 * |z4| * H ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow]
    have : |(2 : ℤ)| = 2 := by norm_num
    rw [this]
    calc 2 * |z4| * |a| * |d| ^ 2 = 2 * |z4| * (|a| * |d| ^ 2) := by ring
      _ ≤ 2 * |z4| * (H * H ^ 2) := by gcongr
      _ = 2 * |z4| * H ^ 3 := by ring
  have e4 : |z6 * d ^ 3| ≤ |z6| * H ^ 3 := by
    rw [abs_mul, abs_pow]
    gcongr
  calc |4 * c * a ^ 3 + z2 * a ^ 2 * d + 2 * z4 * a * d ^ 2 + z6 * d ^ 3|
      ≤ |4 * c * a ^ 3 + z2 * a ^ 2 * d + 2 * z4 * a * d ^ 2| + |z6 * d ^ 3| := abs_add_le _ _
    _ ≤ |4 * c * a ^ 3 + z2 * a ^ 2 * d| + |2 * z4 * a * d ^ 2| + |z6 * d ^ 3| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ |4 * c * a ^ 3| + |z2 * a ^ 2 * d| + |2 * z4 * a * d ^ 2| + |z6 * d ^ 3| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ 4 * |c| * H ^ 3 + |z2| * H ^ 3 + 2 * |z4| * H ^ 3 + |z6| * H ^ 3 := by
        gcongr
    _ = (4 * |c| + |z2| + 2 * |z4| + |z6|) * H ^ 3 := by ring

theorem main : ∀ (b2 b4 b6 b8 : ℚ), ∃ K : ℕ, ∀ x : ℚ,
    4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6 ≠ 0 →
    max ((x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) / (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)).num.natAbs
        ((x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) / (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)).den
      ≤ K * (max x.num.natAbs x.den) ^ 4 := by
  intro b2 b4 b6 b8
  obtain ⟨z2, hz2⟩ := clr b2 (b2.den * b4.den * b6.den * b8.den)
    ⟨b4.den * b6.den * b8.den, by ring⟩
  obtain ⟨z4, hz4⟩ := clr b4 (b2.den * b4.den * b6.den * b8.den)
    ⟨b2.den * b6.den * b8.den, by ring⟩
  obtain ⟨z6, hz6⟩ := clr b6 (b2.den * b4.den * b6.den * b8.den)
    ⟨b2.den * b4.den * b8.den, by ring⟩
  obtain ⟨z8, hz8⟩ := clr b8 (b2.den * b4.den * b6.den * b8.den)
    ⟨b2.den * b4.den * b6.den, by ring⟩
  have hcpos : 0 < b2.den * b4.den * b6.den * b8.den := by positivity
  generalize b2.den * b4.den * b6.den * b8.den = c at hz2 hz4 hz6 hz8 hcpos
  refine ⟨c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
    + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs), ?_⟩
  intro x hx
  have hdpos : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.pos
  have hxa : (x.num : ℚ) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
  set Fi : ℤ := (c : ℤ) * x.num ^ 4 - z4 * x.num ^ 2 * (x.den : ℤ) ^ 2
    - 2 * z6 * x.num * (x.den : ℤ) ^ 3 - z8 * (x.den : ℤ) ^ 4 with hFi
  set Gi : ℤ := 4 * (c : ℤ) * x.num ^ 3 + z2 * x.num ^ 2 * (x.den : ℤ)
    + 2 * z4 * x.num * (x.den : ℤ) ^ 2 + z6 * (x.den : ℤ) ^ 3 with hGi
  have hFq : (Fi : ℚ) = (c : ℚ) * (x.den : ℚ) ^ 4 * (x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) := by
    rw [hFi]
    push_cast
    rw [hxa, ← hz4, ← hz6, ← hz8]
    ring
  have hGq : (Gi : ℚ) = (c : ℚ) * (x.den : ℚ) ^ 3 * (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6) := by
    rw [hGi]
    push_cast
    rw [hxa, ← hz2, ← hz4, ← hz6]
    ring
  have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hd0 : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hGi0 : Gi ≠ 0 := by
    intro h
    have h' : (Gi : ℚ) = 0 := by exact_mod_cast h
    rw [hGq] at h'
    exact (mul_ne_zero (mul_ne_zero hc0 (pow_ne_zero _ hd0)) hx) h'
  have hM0 : (x.den : ℤ) * Gi ≠ 0 := mul_ne_zero hdpos.ne' hGi0
  have hX : (x ^ 4 - b4 * x ^ 2 - 2 * b6 * x - b8) / (4 * x ^ 3 + b2 * x ^ 2 + 2 * b4 * x + b6)
      = (Fi : ℚ) / (((x.den : ℤ) * Gi : ℤ) : ℚ) := by
    push_cast
    rw [hFq, hGq]
    field_simp
  have key := quot_height Fi ((x.den : ℤ) * Gi) _ hM0 hX
  have hH1 : |x.num| ≤ ((max x.num.natAbs x.den : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast le_max_left _ _
  have hH2 : |(x.den : ℤ)| ≤ ((max x.num.natAbs x.den : ℕ) : ℤ) := by
    rw [abs_of_pos hdpos]
    exact_mod_cast le_max_right _ _
  generalize max x.num.natAbs x.den = Hn at hH1 hH2 ⊢
  have hdH : (x.den : ℤ) ≤ (Hn : ℤ) := by
    rw [← abs_of_pos hdpos]
    exact hH2
  have hc' : |(c : ℤ)| = (c : ℤ) := abs_of_nonneg (by positivity)
  have hFb : |Fi| ≤ ((c : ℤ) + |z4| + 2 * |z6| + |z8|) * (Hn : ℤ) ^ 4 := by
    have h := bnd_F x.num (x.den : ℤ) (Hn : ℤ) (c : ℤ) z4 z6 z8 hH1 hH2
    rw [hc'] at h
    rw [hFi]
    exact h
  have hGb : |Gi| ≤ (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) * (Hn : ℤ) ^ 3 := by
    have h := bnd_G x.num (x.den : ℤ) (Hn : ℤ) (c : ℤ) z2 z4 z6 hH1 hH2
    rw [hc'] at h
    rw [hGi]
    exact h
  have hMb : |(x.den : ℤ) * Gi| ≤ (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) * (Hn : ℤ) ^ 4 := by
    rw [abs_mul, abs_of_pos hdpos]
    calc (x.den : ℤ) * |Gi| ≤ (Hn : ℤ) * ((4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) * (Hn : ℤ) ^ 3) :=
          mul_le_mul hdH hGb (abs_nonneg _) (by positivity)
      _ = (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) * (Hn : ℤ) ^ 4 := by ring
  have hKZ : ((c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
      + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs) : ℕ) : ℤ)
      = (c : ℤ) + |z4| + 2 * |z6| + |z8| + (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) := by
    push_cast [Int.natCast_natAbs]
    ring
  have hSF : (0 : ℤ) ≤ (c : ℤ) + |z4| + 2 * |z6| + |z8| := by positivity
  have hSG : (0 : ℤ) ≤ 4 * (c : ℤ) + |z2| + 2 * |z4| + |z6| := by positivity
  have hA : ((Fi.natAbs : ℕ) : ℤ) ≤ (((c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
      + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs) : ℕ) : ℤ)) * (Hn : ℤ) ^ 4 := by
    rw [Int.natCast_natAbs, hKZ]
    calc |Fi| ≤ ((c : ℤ) + |z4| + 2 * |z6| + |z8|) * (Hn : ℤ) ^ 4 := hFb
      _ ≤ ((c : ℤ) + |z4| + 2 * |z6| + |z8| + (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|))
          * (Hn : ℤ) ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hB : (((x.den : ℤ) * Gi).natAbs : ℤ) ≤ (((c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
      + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs) : ℕ) : ℤ)) * (Hn : ℤ) ^ 4 := by
    rw [Int.natCast_natAbs, hKZ]
    calc |(x.den : ℤ) * Gi| ≤ (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|) * (Hn : ℤ) ^ 4 := hMb
      _ ≤ ((c : ℤ) + |z4| + 2 * |z6| + |z8| + (4 * (c : ℤ) + |z2| + 2 * |z4| + |z6|))
          * (Hn : ℤ) ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hA': Fi.natAbs ≤ (c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
      + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs)) * Hn ^ 4 := by
    exact_mod_cast hA
  have hB' : ((x.den : ℤ) * Gi).natAbs ≤ (c + z4.natAbs + 2 * z6.natAbs + z8.natAbs
      + (4 * c + z2.natAbs + 2 * z4.natAbs + z6.natAbs)) * Hn ^ 4 := by
    exact_mod_cast hB
  exact le_trans key (max_le hA' hB')

end MPP.Solutions.Bsd051
