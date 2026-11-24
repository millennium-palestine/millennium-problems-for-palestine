import Mathlib

namespace MPP.Solutions.Bsd018

/-- Split the even leg of a primitive triple with odd leg `O`: `2 E O = b²` gives odd `s` and
`t ≠ 0` with `E² + O² = s⁴ + 4t⁴`. -/
theorem even_split (E O b : ℤ) (hb : b ≠ 0) (hE : Even E) (hO : Odd O)
    (hcop : IsCoprime E O) (h : 2 * E * O = b ^ 2) :
    ∃ s t : ℤ, Odd s ∧ IsCoprime s t ∧ t ≠ 0 ∧ E ^ 2 + O ^ 2 = s ^ 4 + 4 * t ^ 4 := by
  obtain ⟨e, rfl⟩ := hE
  have hbe : Even (b ^ 2) := ⟨2 * e * O, by rw [← h]; ring⟩
  obtain ⟨β, hβ⟩ := (Int.even_pow.mp hbe).1
  have hk : e * O = β ^ 2 := by
    have h4 : (4 : ℤ) * (e * O) = 4 * β ^ 2 := by
      rw [hβ] at h
      linear_combination h
    linarith
  have hcopEO : IsCoprime e O :=
    (show IsCoprime (2 * e) O by rw [show (2 : ℤ) * e = e + e by ring]; exact hcop).of_mul_left_right
  obtain ⟨t, ht⟩ := Int.sq_of_isCoprime hcopEO hk
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime hcopEO.symm (by rw [mul_comm]; exact hk)
  have hsodd : Odd s := by
    have hO2 : Odd (s ^ 2) := by
      rcases hs with hs | hs
      · rw [hs] at hO
        exact hO
      · rw [hs] at hO
        exact Int.odd_iff.mpr (by have := Int.odd_iff.mp hO; omega)
    exact Int.odd_pow.mp hO2 |>.resolve_right (by norm_num)
  have hcopst : IsCoprime s t := by
    have hc : IsCoprime O e := hcopEO.symm
    have h2 : IsCoprime (s ^ 2) (t ^ 2) := by
      rcases hs with hs | hs <;> rcases ht with ht | ht <;> rw [hs, ht] at hc
      · exact hc
      · simpa [IsCoprime.neg_right_iff] using hc
      · simpa [IsCoprime.neg_left_iff] using hc
      · simpa [IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using hc
    exact (IsCoprime.pow_left_iff (by norm_num : 0 < 2)).mp
      ((IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp h2)
  have htne : t ≠ 0 := by
    intro ht0
    apply hb
    have he0 : e = 0 := by
      rw [ht0] at ht
      simpa using ht
    have hb2 : b ^ 2 = 0 := by rw [← h, he0]; ring
    exact pow_eq_zero_iff two_ne_zero |>.mp hb2
  refine ⟨s, t, hsodd, hcopst, htne, ?_⟩
  have hE2 : (e + e) ^ 2 = 4 * t ^ 4 := by
    rcases ht with ht | ht <;> rw [ht] <;> ring
  have hO2 : O ^ 2 = s ^ 4 := by
    rcases hs with hs | hs <;> rw [hs] <;> ring
  rw [hE2, hO2]
  ring

/-- Descent step from `s⁴ + 4t⁴ = a²` with `s` odd: a smaller solution of `p⁴ − q⁴ = c²`. -/
theorem descent_even (s t a : ℤ) (ha : 0 < a) (hs : Odd s) (hst : IsCoprime s t) (ht : t ≠ 0)
    (h : s ^ 4 + 4 * t ^ 4 = a ^ 2) :
    ∃ p q c : ℤ, 0 < p ∧ p < a ∧ 0 < q ∧ 0 < c ∧ Int.gcd p q = 1 ∧ p ^ 4 - q ^ 4 = c ^ 2 := by
  have hpt : PythagoreanTriple (s ^ 2) (2 * t ^ 2) a := by
    unfold PythagoreanTriple
    linear_combination h
  have hcop2 : IsCoprime (s ^ 2) 2 := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨1, -(2 * k ^ 2 + 2 * k), by rw [hk]; ring⟩
  have hgcd : Int.gcd (s ^ 2) (2 * t ^ 2) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]
    exact hcop2.mul_right ((hst.pow_left (m := 2)).pow_right (n := 2))
  have hodd : (s ^ 2) % 2 = 1 := Int.odd_iff.mp hs.pow
  obtain ⟨M, N, hx, hy, hz, hMN, _, hM0⟩ :=
    PythagoreanTriple.coprime_classification' hpt hgcd hodd ha
  have hMNt : M * N = t ^ 2 := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hM : 0 < M := by
    rcases hM0.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      rw [← h1] at hMNt
      simp at hMNt
      linarith
  have hN : 0 < N := by nlinarith
  have hIC : IsCoprime M N := Int.isCoprime_iff_gcd_eq_one.mpr hMN
  obtain ⟨p, hp⟩ := Int.sq_of_isCoprime hIC hMNt
  obtain ⟨q, hq⟩ := Int.sq_of_isCoprime hIC.symm (by rw [mul_comm]; exact hMNt)
  have hMp : M = p ^ 2 := by
    rcases hp with hp | hp
    · exact hp
    · exfalso; nlinarith [sq_nonneg p]
  have hNq : N = q ^ 2 := by
    rcases hq with hq | hq
    · exact hq
    · exfalso; nlinarith [sq_nonneg q]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0] at hMp
    simp at hMp
    linarith
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0] at hNq
    simp at hNq
    linarith
  have hpq : IsCoprime p q := by
    have h2 : IsCoprime (p ^ 2) (q ^ 2) := by
      rw [← hMp, ← hNq]
      exact hIC
    exact (IsCoprime.pow_left_iff (by norm_num : 0 < 2)).mp
      ((IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp h2)
  have hgcdpq : Int.gcd |p| |q| = 1 := by
    have h3 := Int.isCoprime_iff_gcd_eq_one.mp hpq
    unfold Int.gcd at h3 ⊢
    simpa [Int.natAbs_abs] using h3
  have hp4 : |p| ^ 4 = p ^ 4 := by
    rw [show |p| ^ 4 = (|p| ^ 2) ^ 2 by ring, sq_abs]
    ring
  have hq4 : |q| ^ 4 = q ^ 4 := by
    rw [show |q| ^ 4 = (|q| ^ 2) ^ 2 by ring, sq_abs]
    ring
  have hs0 : s ≠ 0 := by
    intro h0
    have := Int.odd_iff.mp hs
    rw [h0] at this
    norm_num at this
  have ha' : a = p ^ 4 + q ^ 4 := by
    rw [hz, hMp, hNq]
    ring
  have hx' : s ^ 2 = p ^ 4 - q ^ 4 := by
    rw [hx, hMp, hNq]
    ring
  refine ⟨|p|, |q|, |s|, abs_pos.mpr hp0, ?_, abs_pos.mpr hq0, abs_pos.mpr hs0, hgcdpq, ?_⟩
  · have hpabs : 1 ≤ |p| := Int.one_le_abs hp0
    have hq4pos : 0 < q ^ 4 := by positivity
    have hr : (0 : ℤ) ≤ |p| - 1 := by linarith
    have e1 := mul_nonneg hr (pow_nonneg (abs_nonneg p) 3)
    have e2 := mul_nonneg hr (pow_nonneg (abs_nonneg p) 2)
    have e3 := mul_nonneg hr (abs_nonneg p)
    have hle : |p| ≤ |p| ^ 4 := by nlinarith
    rw [hp4] at hle
    rw [ha']
    linarith
  · rw [hp4, hq4, sq_abs, hx']

/-- The even case of Fermat's descent: a primitive solution of `a⁴ − b⁴ = c²` with `b` even yields
a smaller one. -/
theorem main : ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c → Int.gcd a b = 1 → a ^ 4 - b ^ 4 = c ^ 2 →
    Even b → ∃ a' b' c' : ℤ, 0 < a' ∧ a' < a ∧ 0 < b' ∧ 0 < c' ∧ Int.gcd a' b' = 1 ∧
      a' ^ 4 - b' ^ 4 = c' ^ 2 := by
  intro a b c ha hb hc hab h hev
  have hb0 : b ≠ 0 := hb.ne'
  have hcopab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hab
  have hb2c2 : IsCoprime (b ^ 2) (c ^ 2) := by
    obtain ⟨u, v, huv⟩ := (hcopab.symm.pow (m := 2) (n := 4))
    exact ⟨u + v * b ^ 2, v, by linear_combination huv - v * h⟩
  have hb2c : IsCoprime (b ^ 2) c := by
    have : IsCoprime (b ^ 2) (c * c) := by
      rw [← pow_two]
      exact hb2c2
    exact this.of_mul_right_left
  have hT : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
    unfold PythagoreanTriple
    linear_combination (-1 : ℤ) * h
  have hgcd : Int.gcd (b ^ 2) c = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb2c
  obtain ⟨m, n, hx, hz, hmn, hpar⟩ := PythagoreanTriple.coprime_classification.mp ⟨hT, hgcd⟩
  have hcase : b ^ 2 = 2 * m * n := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      have h2b : (2 : ℤ) ∣ b ^ 2 := dvd_pow (even_iff_two_dvd.mp hev) two_ne_zero
      have h2c : (2 : ℤ) ∣ c := ⟨m * n, by rw [h2]; ring⟩
      have hu := hb2c.isUnit_of_dvd' h2b h2c
      rw [Int.isUnit_iff] at hu
      omega
    · exact h1
  have hsq : a ^ 2 = m ^ 2 + n ^ 2 := by
    rcases hz with hz | hz
    · exact hz
    · exfalso
      nlinarith [sq_nonneg m, sq_nonneg n, pow_pos ha 2]
  have hsn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
  have key : ∃ s t : ℤ, Odd s ∧ IsCoprime s t ∧ t ≠ 0 ∧ a ^ 2 = s ^ 4 + 4 * t ^ 4 := by
    rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
    · obtain ⟨s, t, h1, h2, h3, h4⟩ :=
        even_split m n b hb0 (Int.even_iff.mpr hm) (Int.odd_iff.mpr hn) hsn hcase.symm
      exact ⟨s, t, h1, h2, h3, by linarith [h4, hsq]⟩
    · obtain ⟨s, t, h1, h2, h3, h4⟩ :=
        even_split n m b hb0 (Int.even_iff.mpr hn) (Int.odd_iff.mpr hm) hsn.symm
          (by rw [hcase]; ring)
      exact ⟨s, t, h1, h2, h3, by linarith [h4, hsq]⟩
  obtain ⟨s, t, hs, hst, ht, hst2⟩ := key
  obtain ⟨p, q, c', hp0, hpa, hq0, hc0, hg, hE⟩ := descent_even s t a ha hs hst ht hst2.symm
  exact ⟨p, q, c', hp0, hpa, hq0, hc0, hg, hE⟩

end MPP.Solutions.Bsd018
