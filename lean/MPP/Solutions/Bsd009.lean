import Mathlib

namespace MPP.Solutions.Bsd009

theorem frac_sq (a b d f : ℤ) (ha : a = d ^ 2 ∨ a = -d ^ 2) (hb : b = f ^ 2 ∨ b = -f ^ 2) :
    ∃ u : ℚ, (a : ℚ) / (b : ℚ) = u ^ 2 ∨ (a : ℚ) / (b : ℚ) = -(u ^ 2) := by
  refine ⟨(d : ℚ) / (f : ℚ), ?_⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;> push_cast
  · exact Or.inl (by rw [div_pow])
  · exact Or.inr (by rw [div_neg, div_pow])
  · exact Or.inr (by rw [neg_div, div_pow])
  · exact Or.inl (by rw [neg_div_neg_eq, div_pow])

theorem frac_sq2 (a b d f : ℤ) (ha : a = 2 * d ^ 2 ∨ a = -(2 * d ^ 2)) (hb : b = f ^ 2 ∨ b = -f ^ 2) :
    ∃ u : ℚ, (a : ℚ) / (b : ℚ) = 2 * u ^ 2 ∨ (a : ℚ) / (b : ℚ) = -(2 * u ^ 2) := by
  refine ⟨(d : ℚ) / (f : ℚ), ?_⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;> push_cast
  · exact Or.inl (by rw [div_pow]; ring)
  · exact Or.inr (by rw [div_neg, div_pow]; ring)
  · exact Or.inr (by rw [neg_div, div_pow]; ring)
  · exact Or.inl (by rw [neg_div_neg_eq, div_pow]; ring)

theorem core (a b : ℤ) (hcop : IsCoprime a b) (s : ℤ) (hs : a * b * (a ^ 2 + 4 * b ^ 2) = s * s) :
    ∃ u : ℚ, (a : ℚ) / (b : ℚ) = u ^ 2 ∨ (a : ℚ) / (b : ℚ) = -(u ^ 2) ∨
      (a : ℚ) / (b : ℚ) = 2 * u ^ 2 ∨ (a : ℚ) / (b : ℚ) = -(2 * u ^ 2) := by
  rcases Int.even_or_odd a with hae | hao
  · -- a even: a = 2A
    obtain ⟨A, hA⟩ := hae
    have ha2 : a = 2 * A := by linarith
    have hb_odd : b % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one b with h0 | h1
      · exfalso
        obtain ⟨j, hj⟩ : ∃ j, b = j + j := ⟨b / 2, by omega⟩
        obtain ⟨u, v, huv⟩ := hcop
        rw [ha2, hj] at huv
        have h2 : (2 : ℤ) * (u * A + v * j) = 1 := by linear_combination huv
        generalize u * A + v * j = t at h2
        omega
      · exact h1
    obtain ⟨j, hj⟩ : ∃ j, b = 2 * j + 1 := ⟨b / 2, by omega⟩
    have hs8 : 8 * (A * b * (A ^ 2 + b ^ 2)) = s * s := by
      rw [ha2] at hs
      linear_combination hs
    have h2s : (2 : ℤ) ∣ s ^ 2 := ⟨4 * (A * b * (A ^ 2 + b ^ 2)), by linear_combination -hs8⟩
    obtain ⟨s1, hs1⟩ := Int.prime_two.dvd_of_dvd_pow h2s
    have hX2 : 2 * (A * b * (A ^ 2 + b ^ 2)) = s1 * s1 := by
      have h4 : 4 * (2 * (A * b * (A ^ 2 + b ^ 2))) = 4 * (s1 * s1) := by
        rw [hs1] at hs8
        linear_combination hs8
      linarith
    have h2s1 : (2 : ℤ) ∣ s1 ^ 2 := ⟨A * b * (A ^ 2 + b ^ 2), by linear_combination -hX2⟩
    obtain ⟨t, ht⟩ := Int.prime_two.dvd_of_dvd_pow h2s1
    have hX : A * b * (A ^ 2 + b ^ 2) = 2 * (t * t) := by
      have h2' : 2 * (A * b * (A ^ 2 + b ^ 2)) = 2 * (2 * (t * t)) := by
        rw [ht] at hX2
        linear_combination hX2
      linarith
    rcases Int.even_or_odd A with hAe | hAo
    · -- A even: A = c + c, so a = 4c and c·b·(4c² + b²) = t²
      obtain ⟨c, hc⟩ := hAe
      have ha4 : a = 4 * c := by rw [ha2, hc]; ring
      have hcop4 : IsCoprime (4 * c) b := by rw [← ha4]; exact hcop
      have hcb : IsCoprime c b := hcop4.of_mul_left_right
      have hcr : IsCoprime c (4 * c ^ 2 + b ^ 2) := by
        have h := (hcb.pow_right (n := 2)).add_mul_left_right (4 * c)
        simpa only [show 4 * c ^ 2 + b ^ 2 = b ^ 2 + c * (4 * c) by ring] using h
      have hbr : IsCoprime b (4 * c ^ 2 + b ^ 2) := by
        have h2 : IsCoprime b 2 := ⟨1, -j, by rw [hj]; ring⟩
        have h4 : IsCoprime b 4 := by
          have := h2.mul_right h2
          norm_num at this
          exact this
        have hbc2 : IsCoprime b (c ^ 2) := hcb.symm.pow_right
        have h3 : IsCoprime b (4 * c ^ 2) := h4.mul_right hbc2
        have h5 := h3.add_mul_left_right b
        simpa only [show 4 * c ^ 2 + b ^ 2 = 4 * c ^ 2 + b * b by ring] using h5
      have e1' : 2 * (c * (b * (4 * c ^ 2 + b ^ 2))) = 2 * (t ^ 2) := by
        rw [hc] at hX
        linear_combination hX
      have e1 : c * (b * (4 * c ^ 2 + b ^ 2)) = t ^ 2 := by linarith
      obtain ⟨d, hd⟩ := Int.sq_of_isCoprime (hcb.mul_right hcr) e1
      have e2 : b * (c * (4 * c ^ 2 + b ^ 2)) = t ^ 2 := by linear_combination e1
      obtain ⟨f, hf⟩ := Int.sq_of_isCoprime (hcb.symm.mul_right hbr) e2
      have hA' : a = (2 * d) ^ 2 ∨ a = -((2 * d) ^ 2) := by
        rcases hd with hd | hd
        · left
          rw [ha4, hd]
          ring
        · right
          rw [ha4, hd]
          ring
      obtain ⟨u, hu⟩ := frac_sq a b (2 * d) f hA' hf
      exact ⟨u, by
        rcases hu with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)⟩
    · -- A odd: A = 2k + 1, m := (A² + b²)/2, and A·b·m = t²
      obtain ⟨k, hk⟩ := hAo
      obtain ⟨m, hm⟩ : ∃ m, A ^ 2 + b ^ 2 = 2 * m :=
        ⟨2 * k ^ 2 + 2 * k + 2 * j ^ 2 + 2 * j + 1, by rw [hk, hj]; ring⟩
      have e1' : 2 * (A * (b * m)) = 2 * (t ^ 2) := by
        linear_combination hX - A * b * hm
      have e1 : A * (b * m) = t ^ 2 := by linarith
      have hAb : IsCoprime A b := by
        have hcop2 : IsCoprime (2 * A) b := ha2 ▸ hcop
        exact hcop2.of_mul_left_right
      have hAm : IsCoprime A m := by
        have h1 : IsCoprime A (A ^ 2 + b ^ 2) := by
          have h := (hAb.pow_right (n := 2)).add_mul_left_right A
          simpa only [show A ^ 2 + b ^ 2 = b ^ 2 + A * A by ring] using h
        rw [hm] at h1
        exact h1.of_mul_right_right
      have hbm : IsCoprime b m := by
        have h1 : IsCoprime b (A ^ 2 + b ^ 2) := by
          have h := (hAb.symm.pow_right (n := 2)).add_mul_left_right b
          simpa only [show A ^ 2 + b ^ 2 = A ^ 2 + b * b by ring] using h
        rw [hm] at h1
        exact h1.of_mul_right_right
      obtain ⟨d, hd⟩ := Int.sq_of_isCoprime (hAb.mul_right hAm) e1
      have e2 : b * (A * m) = t ^ 2 := by linear_combination e1
      obtain ⟨f, hf⟩ := Int.sq_of_isCoprime (hAb.symm.mul_right hbm) e2
      have ha' : a = 2 * d ^ 2 ∨ a = -(2 * d ^ 2) := by
        rcases hd with hd | hd
        · left
          rw [ha2, hd]
        · right
          rw [ha2, hd]
          ring
      obtain ⟨u, hu⟩ := frac_sq2 a b d f ha' hf
      exact ⟨u, by
        rcases hu with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))⟩
  · -- a odd: a = 2k + 1; a, b, a² + 4b² are coprime up to the factor 2
    obtain ⟨k, hk⟩ := hao
    have h2 : IsCoprime a 2 := ⟨1, -k, by rw [hk]; ring⟩
    have h4 : IsCoprime a 4 := by
      have := h2.mul_right h2
      norm_num at this
      exact this
    have hra : IsCoprime a (a ^ 2 + 4 * b ^ 2) := by
      have h := (h4.mul_right (hcop.pow_right (n := 2))).add_mul_left_right a
      simpa only [show a ^ 2 + 4 * b ^ 2 = 4 * b ^ 2 + a * a by ring] using h
    have hrb : IsCoprime b (a ^ 2 + 4 * b ^ 2) := by
      have h := (hcop.symm.pow_right (n := 2)).add_mul_left_right (4 * b)
      simpa only [show a ^ 2 + 4 * b ^ 2 = a ^ 2 + b * (4 * b) by ring] using h
    have e1 : a * (b * (a ^ 2 + 4 * b ^ 2)) = s ^ 2 := by
      rw [sq]
      linear_combination hs
    have e2 : b * (a * (a ^ 2 + 4 * b ^ 2)) = s ^ 2 := by
      rw [sq]
      linear_combination hs
    obtain ⟨d, hd⟩ := Int.sq_of_isCoprime (hcop.mul_right hra) e1
    obtain ⟨f, hf⟩ := Int.sq_of_isCoprime (hcop.symm.mul_right hrb) e2
    obtain ⟨u, hu⟩ := frac_sq a b d f hd hf
    exact ⟨u, by
      rcases hu with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)⟩

theorem sq_of_curve (x y : ℚ) (a b : ℤ) (hb : (b : ℚ) ≠ 0) (hx : x = (a : ℚ) / (b : ℚ))
    (hxy : y ^ 2 = x ^ 3 + 4 * x) : IsSquare ((a * b * (a ^ 2 + 4 * b ^ 2) : ℤ) : ℚ) := by
  refine ⟨y * (b : ℚ) ^ 2, ?_⟩
  have e : (y * (b : ℚ) ^ 2) * (y * (b : ℚ) ^ 2) = y ^ 2 * (b : ℚ) ^ 4 := by ring
  rw [e, hxy, hx]
  push_cast
  field_simp

theorem main : ∀ x y : ℚ, y ^ 2 = x ^ 3 + 4 * x →
    ∃ u : ℚ, x = u ^ 2 ∨ x = -(u ^ 2) ∨ x = 2 * u ^ 2 ∨ x = -(2 * u ^ 2) := by
  intro x y hxy
  by_cases hx0 : x = 0
  · exact ⟨0, Or.inl (by rw [hx0]; ring)⟩
  have hx : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Rat.num_div_den]
  have hbpos : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    show Nat.gcd _ _ = 1
    simpa using x.reduced
  have hb0 : ((x.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
  obtain ⟨s, hs⟩ := Rat.isSquare_intCast_iff.mp (sq_of_curve x y x.num (x.den : ℤ) hb0 hx hxy)
  obtain ⟨u, hu⟩ := core x.num (x.den : ℤ) hcop s hs
  exact ⟨u, by rw [hx]; exact hu⟩

end MPP.Solutions.Bsd009
