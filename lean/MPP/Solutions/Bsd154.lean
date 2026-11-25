import Mathlib

namespace MPP.Solutions.Bsd154

theorem main : ∀ (a q : ℝ) (s : ℕ → ℝ), 0 < q → 4 * q < a ^ 2 → s 0 = 2 → s 1 = a →
    (∀ k : ℕ, s (k + 2) = a * s (k + 1) - q * s k) →
    ∀ C : ℝ, ∃ n : ℕ, C ^ 2 * q ^ n < s n ^ 2 := by
  intro a q s hq hD h0 h1 hrec C
  -- the dominant-root step, for a pair g, d with g d = q and d² < g²
  have aux : ∀ g d : ℝ, g * d = q → d ^ 2 < g ^ 2 → ∀ C : ℝ, ∃ n : ℕ, C ^ 2 * q ^ n < (g ^ n + d ^ n) ^ 2 := by
    intro g d hgd hlt C
    have hq0 : q ≠ 0 := hq.ne'
    have hq2 : q ^ 2 = g ^ 2 * d ^ 2 := by rw [← hgd]; ring
    have hgq : q < g ^ 2 := by
      by_contra hcon
      push_neg at hcon
      have h1' : 0 ≤ (q - g ^ 2) * (q + g ^ 2) :=
        mul_nonneg (sub_nonneg.mpr hcon) (add_nonneg hq.le (sq_nonneg g))
      nlinarith [h1', hq2, mul_pos (sub_pos.mpr hlt) (lt_of_le_of_lt (sq_nonneg d) hlt)]
    have ht : 1 < g ^ 2 / q := (one_lt_div hq).mpr hgq
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C ^ 2) ht
    refine ⟨n, ?_⟩
    have hmul : g ^ 2 / q * q = g ^ 2 := by field_simp
    have hkey : (g ^ 2 / q) ^ n * q ^ n = (g ^ n) ^ 2 := by
      rw [← mul_pow, hmul]
      ring
    have hgdn : g ^ n * d ^ n = q ^ n := by rw [← mul_pow, hgd]
    have hsplit : (g ^ n + d ^ n) ^ 2 = (g ^ n) ^ 2 + 2 * (g ^ n * d ^ n) + (d ^ n) ^ 2 := by ring
    have h3 : C ^ 2 * q ^ n < (g ^ 2 / q) ^ n * q ^ n := mul_lt_mul_of_pos_right hn (pow_pos hq n)
    nlinarith [h3, hkey, hsplit, hgdn, sq_nonneg (d ^ n), pow_pos hq n]
  -- a real square root of the discriminant, and a factorisation q = g d with (g - d)² = a² − 4q
  obtain ⟨r, hr2⟩ : ∃ r : ℝ, r ^ 2 = a ^ 2 - 4 * q :=
    ⟨Real.sqrt (a ^ 2 - 4 * q), Real.sq_sqrt (by linarith)⟩
  obtain ⟨g, d, hsum, hprod, hsq⟩ : ∃ g d : ℝ, g + d = a ∧ g * d = q ∧ (g - d) ^ 2 = a ^ 2 - 4 * q :=
    ⟨(a + r) / 2, (a - r) / 2, by ring, by linear_combination (-1 / 4 : ℝ) * hr2, by linear_combination hr2⟩
  -- the recurrence in the variables g, d
  have hrec' : ∀ k : ℕ, s (k + 1 + 1) = (g + d) * s (k + 1) - (g * d) * s k := fun k => by
    rw [hsum, hprod]
    exact hrec k
  -- closed form s n = g^n + d^n
  have hform : ∀ n : ℕ, s n = g ^ n + d ^ n ∧ s (n + 1) = g ^ (n + 1) + d ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [h0]; norm_num
      · rw [zero_add, h1, pow_one, pow_one, hsum]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec' m, ih.1, ih.2]
      ring
  -- g² ≠ d², since (g - d)(g + d) = 0 would force g = d or a = 0
  have hne : g ^ 2 ≠ d ^ 2 := by
    intro h
    have hprod0 : (g - d) * (g + d) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hprod0 with h2 | h2
    · have : (g - d) ^ 2 = 0 := by rw [h2]; ring
      linarith
    · have ha0 : a = 0 := by linarith
      have : a ^ 2 = 0 := by rw [ha0]; ring
      linarith
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨n, hn⟩ := aux d g (by rw [mul_comm]; exact hprod) hlt C
    refine ⟨n, ?_⟩
    rw [(hform n).1]
    have hswap : (g ^ n + d ^ n) ^ 2 = (d ^ n + g ^ n) ^ 2 := by ring
    rw [hswap]
    exact hn
  · obtain ⟨n, hn⟩ := aux g d hprod hlt C
    exact ⟨n, by rw [(hform n).1]; exact hn⟩

end MPP.Solutions.Bsd154
