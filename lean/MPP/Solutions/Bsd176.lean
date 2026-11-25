import Mathlib

namespace MPP.Solutions.Bsd176

theorem main : ∀ (a p C : ℝ) (c : ℕ → ℝ), 0 < p → c 0 = 1 → c 1 = a →
    (∀ k : ℕ, c (k + 2) = a * c (k + 1) - p * c k) →
    (∀ k : ℕ, |c k| ≤ C * Real.sqrt p ^ k) →
    a ^ 2 ≤ 4 * p := by
  intro a p C c hp h0 h1 hrec hb
  by_contra hcon
  push_neg at hcon
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  have hC : 0 ≤ C := by
    have := hb 0
    simp only [pow_zero, mul_one, h0, Real.norm_eq_abs, abs_one] at this
    linarith
  -- the two-root identity: if x + y = a and x y = p then c (k+1) = y c k + x^(k+1)
  have key : ∀ (x y : ℝ), x + y = a → x * y = p → ∀ k : ℕ,
      c (k + 1) = y * c k + x ^ (k + 1) := by
    intro x y hxy hxyp k
    induction k with
    | zero => simp only [zero_add, pow_one, h0, h1]; linarith
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 from rfl, hrec n]
      linear_combination x * ih + c n * hxyp - c (n + 1) * hxy
  -- growth bound along a root of modulus above √p
  have bnd : ∀ x y : ℝ, x + y = a → x * y = p → Real.sqrt p < |x| → ∀ k : ℕ,
      |x| ^ (k + 1) ≤ 2 * C * Real.sqrt p ^ (k + 1) := by
    intro x y hxy hxyp hx k
    have hxa : |x| * |y| = p := by
      rw [← abs_mul, hxyp, abs_of_pos hp]
    have hy : |y| ≤ Real.sqrt p := by
      nlinarith [abs_nonneg y, abs_nonneg x]
    have hk := key x y hxy hxyp k
    have hdiff : x ^ (k + 1) = c (k + 1) - y * c k := by linarith
    have h2 : |x ^ (k + 1)| ≤ |c (k + 1)| + |y| * |c k| := by
      rw [hdiff]
      exact (abs_sub _ _).trans (by rw [abs_mul])
    rw [abs_pow] at h2
    have h3 := hb (k + 1)
    have h4 := hb k
    have h5 : |y| * |c k| ≤ Real.sqrt p * (C * Real.sqrt p ^ k) :=
      mul_le_mul hy h4 (abs_nonneg _) hs0.le
    calc |x| ^ (k + 1) ≤ |c (k + 1)| + |y| * |c k| := h2
      _ ≤ C * Real.sqrt p ^ (k + 1) + Real.sqrt p * (C * Real.sqrt p ^ k) := add_le_add h3 h5
      _ = 2 * C * Real.sqrt p ^ (k + 1) := by ring
  -- the two roots
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (a ^ 2 - 4 * p) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = a ^ 2 - 4 * p := by rw [hr]; exact Real.sq_sqrt (by linarith)
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (a + r) / 2 := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (a - r) / 2 := ⟨_, rfl⟩
  have hgd : g + d = a := by rw [hg, hd]; ring
  have hgdp : g * d = p := by rw [hg, hd]; linear_combination (-1 / 4) * hr2
  have hrgd : g - d = r := by rw [hg, hd]; ring
  -- one of the two roots has modulus above √p
  have hcase : Real.sqrt p < |g| ∨ Real.sqrt p < |d| := by
    by_contra hno
    push_neg at hno
    obtain ⟨hg1, hd1⟩ := hno
    have hprod : |g| * |d| = p := by rw [← abs_mul, hgdp, abs_of_pos hp]
    have hg' : |g| = Real.sqrt p := by
      nlinarith [abs_nonneg g, abs_nonneg d, mul_nonneg hs0.le (sub_nonneg.2 hd1),
        mul_nonneg (abs_nonneg d) (sub_nonneg.2 hg1)]
    have hd' : |d| = Real.sqrt p := by
      nlinarith [abs_nonneg g, abs_nonneg d, mul_nonneg hs0.le (sub_nonneg.2 hd1),
        mul_nonneg (abs_nonneg d) (sub_nonneg.2 hg1)]
    have hgsq : g ^ 2 = p := by rw [← sq_abs g, hg', hs2]
    have hdsq : d ^ 2 = p := by rw [← sq_abs d, hd', hs2]
    have hg0 : g ≠ 0 := by
      intro h0'
      rw [h0', zero_mul] at hgdp
      linarith
    have hgd_eq : g = d := by
      apply mul_left_cancel₀ hg0
      nlinarith [hgsq, hgdp]
    linarith
  -- the bound contradicts exponential growth of |x| / √p
  obtain ⟨x, y, hxy, hxyp, hx⟩ : ∃ x y : ℝ, x + y = a ∧ x * y = p ∧ Real.sqrt p < |x| := by
    rcases hcase with h | h
    · exact ⟨g, d, hgd, hgdp, h⟩
    · exact ⟨d, g, by linarith, by linarith [hgdp], h⟩
  have hratio : 1 < |x| / Real.sqrt p := (one_lt_div hs0).mpr hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * C) hratio
  have hb' := bnd x y hxy hxyp hx n
  have hpow : (|x| / Real.sqrt p) ^ (n + 1) ≤ 2 * C := by
    rw [div_pow, div_le_iff₀ (pow_pos hs0 (n + 1))]
    exact hb'
  have hmono : (|x| / Real.sqrt p) ^ n ≤ (|x| / Real.sqrt p) ^ (n + 1) :=
    pow_le_pow_right₀ hratio.le (Nat.le_succ n)
  linarith

end MPP.Solutions.Bsd176
