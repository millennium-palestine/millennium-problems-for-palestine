import Mathlib

namespace MPP.Solutions.Bsd050

-- rational root height (as in bsd-047)
theorem root_height : ∀ (A B C : ℤ) (u : ℚ), A ≠ 0 → (A : ℚ) * u ^ 2 + (B : ℚ) * u + (C : ℚ) = 0 →
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

-- clearing denominators
theorem clr (b : ℚ) (c : ℕ) (hc : b.den ∣ c) : ∃ z : ℤ, (c : ℚ) * b = z := by
  obtain ⟨k, hk⟩ := hc
  refine ⟨k * b.num, ?_⟩
  rw [hk]
  push_cast
  linear_combination (k : ℚ) * Rat.mul_den_eq_num b

-- a product of four integers bounded by X, Y, Z, W
theorem prod_bound4 (x y z w X Y Z W : ℤ) (hx : |x| ≤ X) (hy : |y| ≤ Y) (hz : |z| ≤ Z)
    (hw : |w| ≤ W) : |x * y * z * w| ≤ X * Y * Z * W := by
  have hX : 0 ≤ X := le_trans (abs_nonneg x) hx
  have hY : 0 ≤ Y := le_trans (abs_nonneg y) hy
  have hZ : 0 ≤ Z := le_trans (abs_nonneg z) hz
  have hW : 0 ≤ W := le_trans (abs_nonneg w) hw
  rw [abs_mul, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hX) hz (by positivity)
    (mul_nonneg hX hY)) hw (abs_nonneg _) (mul_nonneg (mul_nonneg hX hY) hZ)

-- a sum of five terms with coefficients c_k and monomials bounded by M
theorem five_bound (c1 c2 c3 c4 c5 m1 m2 m3 m4 m5 M : ℤ) (h1 : |m1| ≤ M) (h2 : |m2| ≤ M)
    (h3 : |m3| ≤ M) (h4 : |m4| ≤ M) (h5 : |m5| ≤ M) :
    |c1 * m1 + c2 * m2 + c3 * m3 + c4 * m4 + c5 * m5| ≤ (|c1| + |c2| + |c3| + |c4| + |c5|) * M := by
  have e1 : |c1 * m1| ≤ |c1| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have e2 : |c2 * m2| ≤ |c2| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have e3 : |c3 * m3| ≤ |c3| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  have e4 : |c4 * m4| ≤ |c4| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  have e5 : |c5 * m5| ≤ |c5| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
  have f1 := abs_add_le (c1 * m1 + c2 * m2 + c3 * m3 + c4 * m4) (c5 * m5)
  have f2 := abs_add_le (c1 * m1 + c2 * m2 + c3 * m3) (c4 * m4)
  have f3 := abs_add_le (c1 * m1 + c2 * m2) (c3 * m3)
  have f4 := abs_add_le (c1 * m1) (c2 * m2)
  have hsum : (|c1| + |c2| + |c3| + |c4| + |c5|) * M
      = |c1| * M + |c2| * M + |c3| * M + |c4| * M + |c5| * M := by ring
  rw [hsum]
  linarith

-- a sum of six terms with coefficients c_k and monomials bounded by M
theorem six_bound (c1 c2 c3 c4 c5 c6 m1 m2 m3 m4 m5 m6 M : ℤ) (h1 : |m1| ≤ M)
    (h2 : |m2| ≤ M) (h3 : |m3| ≤ M) (h4 : |m4| ≤ M) (h5 : |m5| ≤ M) (h6 : |m6| ≤ M) :
    |c1 * m1 + c2 * m2 + c3 * m3 + c4 * m4 + c5 * m5 + c6 * m6|
      ≤ (|c1| + |c2| + |c3| + |c4| + |c5| + |c6|) * M := by
  have e6 : |c6 * m6| ≤ |c6| * M := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
  have f1 := abs_add_le (c1 * m1 + c2 * m2 + c3 * m3 + c4 * m4 + c5 * m5) (c6 * m6)
  have g := five_bound c1 c2 c3 c4 c5 m1 m2 m3 m4 m5 M h1 h2 h3 h4 h5
  have hsum : (|c1| + |c2| + |c3| + |c4| + |c5| + |c6|) * M
      = (|c1| + |c2| + |c3| + |c4| + |c5|) * M + |c6| * M := by ring
  rw [hsum]
  linarith

theorem main : ∀ (a1 a2 a3 a4 a6 : ℚ), ∃ K : ℕ, ∀ (x1 x2 s p u : ℚ), x1 ≠ x2 →
    (x1 - x2) ^ 2 * s = 2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2 + a1 ^ 2 * x1 * x2
        + a1 * a3 * (x1 + x2) + 4 * a2 * x1 * x2 + a3 ^ 2 + 2 * a4 * (x1 + x2) + 4 * a6 →
    (x1 - x2) ^ 2 * p = x1 ^ 2 * x2 ^ 2 - a1 * a3 * x1 * x2 - 2 * a4 * x1 * x2
        - a3 ^ 2 * (x1 + x2) - 4 * a6 * (x1 + x2) + a4 ^ 2 - a1 ^ 2 * a6 + a1 * a3 * a4
        - a2 * a3 ^ 2 - 4 * a2 * a6 →
    u ^ 2 - s * u + p = 0 →
    max u.num.natAbs u.den ≤ K * (max x1.num.natAbs x1.den) ^ 2 * (max x2.num.natAbs x2.den) ^ 2 := by
  intro a1 a2 a3 a4 a6
  obtain ⟨D, hDpos, w1, w2, w3, w4, w6, hw1, hw2, hw3, hw4, hw6⟩ : ∃ D : ℕ, 0 < D ∧ ∃ w1 w2 w3 w4 w6 : ℤ,
      (D : ℚ) * a1 = w1 ∧ (D : ℚ) * a2 = w2 ∧ (D : ℚ) * a3 = w3 ∧ (D : ℚ) * a4 = w4 ∧
        (D : ℚ) * a6 = w6 := by
    refine ⟨a1.den * a2.den * a3.den * a4.den * a6.den, by positivity, ?_⟩
    obtain ⟨v1, h1⟩ := clr a1 (a1.den * a2.den * a3.den * a4.den * a6.den)
      ⟨a2.den * a3.den * a4.den * a6.den, by ring⟩
    obtain ⟨v2, h2⟩ := clr a2 (a1.den * a2.den * a3.den * a4.den * a6.den)
      ⟨a1.den * a3.den * a4.den * a6.den, by ring⟩
    obtain ⟨v3, h3⟩ := clr a3 (a1.den * a2.den * a3.den * a4.den * a6.den)
      ⟨a1.den * a2.den * a4.den * a6.den, by ring⟩
    obtain ⟨v4, h4⟩ := clr a4 (a1.den * a2.den * a3.den * a4.den * a6.den)
      ⟨a1.den * a2.den * a3.den * a6.den, by ring⟩
    obtain ⟨v6, h6⟩ := clr a6 (a1.den * a2.den * a3.den * a4.den * a6.den)
      ⟨a1.den * a2.den * a3.den * a4.den, by ring⟩
    exact ⟨v1, v2, v3, v4, v6, h1, h2, h3, h4, h6⟩
  -- integer coefficients of the integer quadratic A u² + (−B) u + C = 0
  obtain ⟨cQ21, hcQ21⟩ : ∃ z : ℤ, z = 2 * (D : ℤ) ^ 3 := ⟨_, rfl⟩
  obtain ⟨cQ11, hcQ11⟩ : ∃ z : ℤ, z = (D : ℤ) * w1 ^ 2 + 4 * (D : ℤ) ^ 2 * w2 := ⟨_, rfl⟩
  obtain ⟨cQ10, hcQ10⟩ : ∃ z : ℤ, z = (D : ℤ) * w1 * w3 + 2 * (D : ℤ) ^ 2 * w4 := ⟨_, rfl⟩
  obtain ⟨cQ00, hcQ00⟩ : ∃ z : ℤ, z = (D : ℤ) * w3 ^ 2 + 4 * (D : ℤ) ^ 2 * w6 := ⟨_, rfl⟩
  obtain ⟨cR22, hcR22⟩ : ∃ z : ℤ, z = (D : ℤ) ^ 3 := ⟨_, rfl⟩
  obtain ⟨cR11, hcR11⟩ : ∃ z : ℤ, z = -((D : ℤ) * w1 * w3 + 2 * (D : ℤ) ^ 2 * w4) := ⟨_, rfl⟩
  obtain ⟨cR10, hcR10⟩ : ∃ z : ℤ, z = -((D : ℤ) * w3 ^ 2 + 4 * (D : ℤ) ^ 2 * w6) := ⟨_, rfl⟩
  obtain ⟨cR00, hcR00⟩ : ∃ z : ℤ, z = (D : ℤ) * w4 ^ 2 - w1 ^ 2 * w6 + w1 * w3 * w4 - w2 * w3 ^ 2
      - 4 * (D : ℤ) * w2 * w6 := ⟨_, rfl⟩
  refine ⟨4 * D ^ 3 + (cQ21.natAbs + cQ21.natAbs + cQ11.natAbs + cQ10.natAbs + cQ10.natAbs
      + cQ00.natAbs) + (cR22.natAbs + cR11.natAbs + cR10.natAbs + cR10.natAbs + cR00.natAbs), ?_⟩
  intro x1 x2 s p u hne hs hp hu
  -- the x-coordinates as fractions a/d and b/e, with the naive heights
  obtain ⟨a, d, hdpos, hx1, hA1, hD1⟩ : ∃ a d : ℤ, 0 < d ∧ x1 = (a : ℚ) / (d : ℚ) ∧
      |a| ≤ ((max x1.num.natAbs x1.den : ℕ) : ℤ) ∧ |d| ≤ ((max x1.num.natAbs x1.den : ℕ) : ℤ) :=
    ⟨x1.num, x1.den, by exact_mod_cast x1.pos, by push_cast; exact (Rat.num_div_den x1).symm,
      by rw [← Int.natCast_natAbs]; exact_mod_cast le_max_left _ _,
      by rw [abs_of_pos (by exact_mod_cast x1.pos)]; exact_mod_cast le_max_right _ _⟩
  obtain ⟨b, e, hepos, hx2, hB1, hE1⟩ : ∃ b e : ℤ, 0 < e ∧ x2 = (b : ℚ) / (e : ℚ) ∧
      |b| ≤ ((max x2.num.natAbs x2.den : ℕ) : ℤ) ∧ |e| ≤ ((max x2.num.natAbs x2.den : ℕ) : ℤ) :=
    ⟨x2.num, x2.den, by exact_mod_cast x2.pos, by push_cast; exact (Rat.num_div_den x2).symm,
      by rw [← Int.natCast_natAbs]; exact_mod_cast le_max_left _ _,
      by rw [abs_of_pos (by exact_mod_cast x2.pos)]; exact_mod_cast le_max_right _ _⟩
  generalize max x1.num.natAbs x1.den = H1 at hA1 hD1 ⊢
  generalize max x2.num.natAbs x2.den = H2 at hB1 hE1 ⊢
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast hepos.ne'
  -- the integer quantities
  have hne' : a * e - b * d ≠ 0 := by
    intro h
    apply hne
    have h' : (a : ℚ) * e = b * d := by exact_mod_cast sub_eq_zero.mp h
    rw [hx1, hx2, div_eq_div_iff hd0 he0]
    linear_combination h'
  -- polynomial relation for u, with x1 and x2 still general
  have hT : (x1 - x2) ^ 2 * u ^ 2 - (2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2 + a1 ^ 2 * x1 * x2
        + a1 * a3 * (x1 + x2) + 4 * a2 * x1 * x2 + a3 ^ 2 + 2 * a4 * (x1 + x2) + 4 * a6) * u
        + (x1 ^ 2 * x2 ^ 2 - a1 * a3 * x1 * x2 - 2 * a4 * x1 * x2
        - a3 ^ 2 * (x1 + x2) - 4 * a6 * (x1 + x2) + a4 ^ 2 - a1 ^ 2 * a6 + a1 * a3 * a4
        - a2 * a3 ^ 2 - 4 * a2 * a6) = 0 := by
    linear_combination (x1 - x2) ^ 2 * hu + u * hs - hp
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hD0q : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  -- the integer forms of the quadratic in u, with their rational identities
  set AZ : ℤ := (D : ℤ) ^ 3 * (a * e - b * d) ^ 2 with hAZ
  set BZ : ℤ := cQ21 * (a * a * b * e) + cQ21 * (a * b * b * d) + cQ11 * (a * b * d * e)
    + cQ10 * (a * d * e * e) + cQ10 * (b * d * d * e) + cQ00 * (d * d * e * e) with hBZ
  set CZ : ℤ := cR22 * (a * a * b * b) + cR11 * (a * b * d * e) + cR10 * (a * d * e * e)
    + cR10 * (b * d * d * e) + cR00 * (d * d * e * e) with hCZ
  have hAq : (AZ : ℚ) = (D : ℚ) ^ 3 * ((d : ℚ) * e) ^ 2 * (x1 - x2) ^ 2 := by
    rw [hAZ, hx1, hx2]
    push_cast
    field_simp
  have hBq : (BZ : ℚ) = (D : ℚ) ^ 3 * ((d : ℚ) * e) ^ 2 * (2 * x1 ^ 2 * x2 + 2 * x1 * x2 ^ 2
        + a1 ^ 2 * x1 * x2 + a1 * a3 * (x1 + x2) + 4 * a2 * x1 * x2 + a3 ^ 2
        + 2 * a4 * (x1 + x2) + 4 * a6) := by
    rw [hBZ, hcQ21, hcQ11, hcQ10, hcQ00]
    push_cast
    rw [← hw1, ← hw2, ← hw3, ← hw4, ← hw6, hx1, hx2]
    field_simp
    ring
  have hCq : (CZ : ℚ) = (D : ℚ) ^ 3 * ((d : ℚ) * e) ^ 2 * (x1 ^ 2 * x2 ^ 2 - a1 * a3 * x1 * x2
        - 2 * a4 * x1 * x2 - a3 ^ 2 * (x1 + x2) - 4 * a6 * (x1 + x2) + a4 ^ 2 - a1 ^ 2 * a6
        + a1 * a3 * a4 - a2 * a3 ^ 2 - 4 * a2 * a6) := by
    rw [hCZ, hcR22, hcR11, hcR10, hcR00]
    push_cast
    rw [← hw1, ← hw2, ← hw3, ← hw4, ← hw6, hx1, hx2]
    field_simp
    ring
  have hquadQ : (AZ : ℚ) * u ^ 2 + (-(BZ : ℚ)) * u + (CZ : ℚ) = 0 := by
    rw [hAq, hBq, hCq]
    linear_combination ((D : ℚ) ^ 3 * ((d : ℚ) * e) ^ 2) * hT
  have hAne : AZ ≠ 0 := by
    rw [hAZ]
    exact mul_ne_zero (pow_ne_zero _ hD0) (pow_ne_zero _ hne')
  have hroot := root_height AZ (-BZ) CZ u hAne (by push_cast; linear_combination hquadQ)
  obtain ⟨hnum, hden⟩ := hroot
  have hH1 : (0 : ℤ) ≤ (H1 : ℤ) := by positivity
  have hH2 : (0 : ℤ) ≤ (H2 : ℤ) := by positivity
  -- bounds on the monomials
  have mA : |a * a * b * e| ≤ (H1 : ℤ) * H1 * H2 * H2 := prod_bound4 _ _ _ _ _ _ _ _ hA1 hA1 hB1 hE1
  have mB : |a * b * b * d| ≤ (H1 : ℤ) * H1 * H2 * H2 :=
    (prod_bound4 _ _ _ _ _ _ _ _ hA1 hB1 hB1 hD1).trans (le_of_eq (by ring))
  have mC : |a * b * d * e| ≤ (H1 : ℤ) * H1 * H2 * H2 :=
    (prod_bound4 _ _ _ _ _ _ _ _ hA1 hB1 hD1 hE1).trans (le_of_eq (by ring))
  have mD : |a * d * e * e| ≤ (H1 : ℤ) * H1 * H2 * H2 := prod_bound4 _ _ _ _ _ _ _ _ hA1 hD1 hE1 hE1
  have mE : |b * d * d * e| ≤ (H1 : ℤ) * H1 * H2 * H2 :=
    (prod_bound4 _ _ _ _ _ _ _ _ hB1 hD1 hD1 hE1).trans (le_of_eq (by ring))
  have mF : |d * d * e * e| ≤ (H1 : ℤ) * H1 * H2 * H2 := prod_bound4 _ _ _ _ _ _ _ _ hD1 hD1 hE1 hE1
  have mG : |a * a * b * b| ≤ (H1 : ℤ) * H1 * H2 * H2 := prod_bound4 _ _ _ _ _ _ _ _ hA1 hA1 hB1 hB1
  have hBb : |BZ| ≤ (|cQ21| + |cQ21| + |cQ11| + |cQ10| + |cQ10| + |cQ00|)
      * ((H1 : ℤ) * H1 * H2 * H2) :=
    six_bound _ _ _ _ _ _ _ _ _ _ _ _ _ mA mB mC mD mE mF
  have hCb : |CZ| ≤ (|cR22| + |cR11| + |cR10| + |cR10| + |cR00|) * ((H1 : ℤ) * H1 * H2 * H2) :=
    five_bound _ _ _ _ _ _ _ _ _ _ _ mG mC mD mE mF
  -- bound on the leading coefficient (a e − b d)² D³
  have hae : |a * e| ≤ (H1 : ℤ) * H2 := by
    rw [abs_mul]; exact mul_le_mul hA1 hE1 (abs_nonneg _) hH1
  have hbd : |b * d| ≤ (H2 : ℤ) * H1 := by
    rw [abs_mul]; exact mul_le_mul hB1 hD1 (abs_nonneg _) hH2
  have hpair : |a * e - b * d| ≤ 2 * (H1 : ℤ) * H2 := by
    calc |a * e - b * d| ≤ |a * e| + |b * d| := abs_sub _ _
      _ ≤ (H1 : ℤ) * H2 + (H2 : ℤ) * H1 := add_le_add hae hbd
      _ = 2 * (H1 : ℤ) * H2 := by ring
  have hsq : (a * e - b * d) ^ 2 ≤ (2 * (H1 : ℤ) * H2) ^ 2 := by
    rw [← sq_abs (a * e - b * d)]
    gcongr
  have hAb : |AZ| ≤ 4 * (D : ℤ) ^ 3 * ((H1 : ℤ) * H1 * H2 * H2) := by
    rw [hAZ, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (D : ℤ) ^ 3),
      abs_of_nonneg (sq_nonneg _)]
    calc (D : ℤ) ^ 3 * (a * e - b * d) ^ 2 ≤ (D : ℤ) ^ 3 * (2 * (H1 : ℤ) * H2) ^ 2 := by gcongr
      _ = 4 * (D : ℤ) ^ 3 * ((H1 : ℤ) * H1 * H2 * H2) := by ring
  -- the constant K, as an integer
  have hSQ0 : (0 : ℤ) ≤ |cQ21| + |cQ21| + |cQ11| + |cQ10| + |cQ10| + |cQ00| := by positivity
  have hSR0 : (0 : ℤ) ≤ |cR22| + |cR11| + |cR10| + |cR10| + |cR00| := by positivity
  have hD3 : (0 : ℤ) ≤ 4 * (D : ℤ) ^ 3 := by positivity
  have hM0 : (0 : ℤ) ≤ (H1 : ℤ) * H1 * H2 * H2 := by positivity
  have hKZ : ((4 * D ^ 3 + (cQ21.natAbs + cQ21.natAbs + cQ11.natAbs + cQ10.natAbs + cQ10.natAbs
      + cQ00.natAbs) + (cR22.natAbs + cR11.natAbs + cR10.natAbs + cR10.natAbs + cR00.natAbs) : ℕ) : ℤ)
      = 4 * (D : ℤ) ^ 3 + (|cQ21| + |cQ21| + |cQ11| + |cQ10| + |cQ10| + |cQ00|)
        + (|cR22| + |cR11| + |cR10| + |cR10| + |cR00|) := by
    push_cast [Int.natCast_natAbs]
    ring
  generalize (4 * D ^ 3 + (cQ21.natAbs + cQ21.natAbs + cQ11.natAbs + cQ10.natAbs + cQ10.natAbs
      + cQ00.natAbs) + (cR22.natAbs + cR11.natAbs + cR10.natAbs + cR10.natAbs + cR00.natAbs) : ℕ) = K
    at hKZ ⊢
  have hAle : |AZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := by
    rw [hKZ]
    exact hAb.trans (mul_le_mul_of_nonneg_right (by linarith) hM0)
  have hBle : |BZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := by
    rw [hKZ]
    exact hBb.trans (mul_le_mul_of_nonneg_right (by linarith) hM0)
  have hCle : |CZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := by
    rw [hKZ]
    exact hCb.trans (mul_le_mul_of_nonneg_right (by linarith) hM0)
  have hAn : AZ.natAbs ≤ K * H1 ^ 2 * H2 ^ 2 := by
    have h : ((AZ.natAbs : ℕ) : ℤ) ≤ ((K * H1 ^ 2 * H2 ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      calc |AZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := hAle
        _ = (K : ℤ) * (H1 : ℤ) ^ 2 * (H2 : ℤ) ^ 2 := by ring
    exact_mod_cast h
  have hBn : (-BZ).natAbs ≤ K * H1 ^ 2 * H2 ^ 2 := by
    have h : (((-BZ).natAbs : ℕ) : ℤ) ≤ ((K * H1 ^ 2 * H2 ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_neg]
      push_cast
      calc |BZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := hBle
        _ = (K : ℤ) * (H1 : ℤ) ^ 2 * (H2 : ℤ) ^ 2 := by ring
    exact_mod_cast h
  have hCn : CZ.natAbs ≤ K * H1 ^ 2 * H2 ^ 2 := by
    have h : ((CZ.natAbs : ℕ) : ℤ) ≤ ((K * H1 ^ 2 * H2 ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      calc |CZ| ≤ (K : ℤ) * ((H1 : ℤ) * H1 * H2 * H2) := hCle
        _ = (K : ℤ) * (H1 : ℤ) ^ 2 * (H2 : ℤ) ^ 2 := by ring
    exact_mod_cast h
  exact max_le ((hnum.trans (max_le hAn (max_le hBn hCn))).trans le_rfl) (hden.trans hAn)

end MPP.Solutions.Bsd050
