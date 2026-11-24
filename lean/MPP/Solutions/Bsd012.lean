import Mathlib

namespace MPP.Solutions.Bsd012

theorem natAbs_le_pow4 (p : ℤ) (hp : p ≠ 0) : (p.natAbs : ℤ) ≤ p ^ 4 := by
  have h1 : |p| ^ 4 = p ^ 4 := by
    rw [pow_abs, abs_of_nonneg (by positivity)]
  have h2 : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
  have h3 : (p.natAbs : ℤ) = |p| := (Int.abs_eq_natAbs p).symm
  rw [h3, ← h1]
  exact le_self_pow₀ h2 (by norm_num)

theorem e2_from (p q r a : ℤ) (hpq : IsCoprime p q) (hr : p * q = r ^ 2) (hp : p ≠ 0)
    (hq : q ≠ 0) (he : (2 * p) ^ 2 + q ^ 2 = a ^ 2) :
    ∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ x ^ 4 + 4 * y ^ 4 = a ^ 2 := by
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime (c := r) hpq hr
  obtain ⟨t, ht⟩ := Int.sq_of_isCoprime (c := r) hpq.symm (by linear_combination hr)
  have hp2 : p ^ 2 = s ^ 4 := by
    rcases hs with h | h <;> rw [h] <;> ring
  have hq2 : q ^ 2 = t ^ 4 := by
    rcases ht with h | h <;> rw [h] <;> ring
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hp
    rcases hs with h | h <;> simp [h]
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hq
    rcases ht with h | h <;> simp [h]
  exact ⟨t, s, ht0, hs0, by linear_combination he - 4 * hp2 - hq2⟩

theorem E2_gcd (N : ℕ)
    (H2 : ∀ x y z : ℤ, z.natAbs ≤ N → x ^ 4 + 4 * y ^ 4 = z ^ 2 → x ≠ 0 → y ≠ 0 → z ≠ 0 → False)
    (g : ℕ) (x' y' z : ℤ) (hg : 2 ≤ g)
    (hE : ((g : ℤ) * x') ^ 4 + 4 * ((g : ℤ) * y') ^ 4 = z ^ 2)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) (hz : z ≠ 0) (hN : z.natAbs = N + 1) : False := by
  have hdvd : ((g : ℤ) ^ 2) ^ 2 ∣ z ^ 2 :=
    ⟨x' ^ 4 + 4 * y' ^ 4, by linear_combination -hE⟩
  obtain ⟨z', hz'⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have h4 : (g : ℤ) ^ 4 * (x' ^ 4 + 4 * y' ^ 4) = (g : ℤ) ^ 4 * z' ^ 2 := by
    rw [hz'] at hE
    linear_combination hE
  have hE2 : x' ^ 4 + 4 * y' ^ 4 = z' ^ 2 := mul_left_cancel₀ (pow_ne_zero 4 hg0) h4
  have hz'0 : z' ≠ 0 := by
    rintro rfl
    apply hz
    rw [hz']
    ring
  have hnat : z.natAbs = g ^ 2 * z'.natAbs := by
    rw [hz', Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hg2 : 4 ≤ g ^ 2 := by nlinarith
  have hzN : z'.natAbs ≤ N := by nlinarith [Nat.zero_le z'.natAbs, hnat, hN, hg2]
  exact H2 x' y' z' hzN hE2 hx' hy' hz'0

theorem E1_gcd (N : ℕ)
    (H1 : ∀ a b c : ℤ, a.natAbs ≤ N → a ^ 4 - b ^ 4 = c ^ 2 → a ≠ 0 → b ≠ 0 → c ≠ 0 → False)
    (g : ℕ) (a' b' c : ℤ) (hg : 2 ≤ g)
    (hE : ((g : ℤ) * a') ^ 4 - ((g : ℤ) * b') ^ 4 = c ^ 2)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc : c ≠ 0) (hN : ((g : ℤ) * a').natAbs = N + 1) : False := by
  have hdvd : ((g : ℤ) ^ 2) ^ 2 ∣ c ^ 2 :=
    ⟨a' ^ 4 - b' ^ 4, by linear_combination -hE⟩
  obtain ⟨c', hc'⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have h4 : (g : ℤ) ^ 4 * (a' ^ 4 - b' ^ 4) = (g : ℤ) ^ 4 * c' ^ 2 := by
    rw [hc'] at hE
    linear_combination hE
  have hE2 : a' ^ 4 - b' ^ 4 = c' ^ 2 := mul_left_cancel₀ (pow_ne_zero 4 hg0) h4
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    apply hc
    rw [hc']
    ring
  have hnat : ((g : ℤ) * a').natAbs = g * a'.natAbs := by
    rw [Int.natAbs_mul]
    simp
  have hNa : a'.natAbs ≤ N := by nlinarith [Nat.zero_le a'.natAbs, hnat, hN, hg]
  exact H1 a' b' c' hNa hE2 ha' hb' hc'0

theorem step2 (N : ℕ)
    (H1 : ∀ a b c : ℤ, a.natAbs ≤ N → a ^ 4 - b ^ 4 = c ^ 2 → a ≠ 0 → b ≠ 0 → c ≠ 0 → False)
    (H2 : ∀ x y z : ℤ, z.natAbs ≤ N → x ^ 4 + 4 * y ^ 4 = z ^ 2 → x ≠ 0 → y ≠ 0 → z ≠ 0 → False) :
    ∀ x y z : ℤ, z.natAbs ≤ N + 1 → x ^ 4 + 4 * y ^ 4 = z ^ 2 → x ≠ 0 → y ≠ 0 → z ≠ 0 → False := by
  intro x y z hzN hE hx hy hz
  by_cases hsmall : z.natAbs ≤ N
  · exact H2 x y z hsmall hE hx hy hz
  have hzN' : z.natAbs = N + 1 := by omega
  by_cases hg : Int.gcd x y = 1
  · have hcop : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hg
    rcases Int.even_or_odd x with hxe | hxo
    · -- x even: z is even, and (y, x/2, z/2) is a smaller solution
      obtain ⟨x2, hx2⟩ := hxe
      have hdz : (2 : ℤ) ∣ z ^ 2 := ⟨8 * x2 ^ 4 + 2 * y ^ 4, by rw [← hE, hx2]; ring⟩
      obtain ⟨z2, hz2⟩ := Int.prime_two.dvd_of_dvd_pow hdz
      have h4 : 4 * (y ^ 4 + 4 * x2 ^ 4) = 4 * z2 ^ 2 := by
        rw [hx2, hz2] at hE
        linear_combination hE
      have hE' : y ^ 4 + 4 * x2 ^ 4 = z2 ^ 2 := by linarith
      have hx2ne : x2 ≠ 0 := by
        rintro rfl
        apply hx
        rw [hx2]
        ring
      have hz2ne : z2 ≠ 0 := by
        rintro rfl
        apply hz
        rw [hz2]
        ring
      have hnz2 : z2.natAbs ≤ N := by
        rw [hz2, Int.natAbs_mul] at hzN'
        simp at hzN'
        omega
      exact H2 y x2 z2 hnz2 hE' hy hx2ne hz2ne
    · -- x odd: (x², 2y², |z|) is a primitive triple, which gives a smaller E1 solution (p, q, x)
      have hxsq : x ^ 2 % 2 = 1 := Int.odd_iff.mp hxo.pow
      have hc1 : IsCoprime x 2 := by
        obtain ⟨k, hk⟩ := hxo
        exact ⟨1, -k, by rw [hk]; ring⟩
      have hc2 : IsCoprime (x ^ 2) (2 * y ^ 2) := by
        have h1 : IsCoprime (x ^ 2) 2 := hc1.pow_left
        have h2 : IsCoprime (x ^ 2) (y ^ 2) := hcop.pow
        exact h1.mul_right h2
      have hgcd : Int.gcd (x ^ 2) (2 * y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hc2
      have htri : PythagoreanTriple (x ^ 2) (2 * y ^ 2) |z| := by
        unfold PythagoreanTriple
        rw [abs_mul_abs_self]
        linear_combination hE
      obtain ⟨m, nn, hm1, hm2, hm3, hmn, _, _⟩ :=
        PythagoreanTriple.coprime_classification' htri hgcd hxsq (abs_pos.mpr hz)
      have hymn : m * nn = y ^ 2 := by linarith
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hy
        have h0 : y ^ 2 = 0 := by rw [← hymn]; ring
        exact (pow_eq_zero_iff two_ne_zero).mp h0
      have hnn0 : nn ≠ 0 := by
        rintro rfl
        apply hy
        have h0 : y ^ 2 = 0 := by rw [← hymn]; ring
        exact (pow_eq_zero_iff two_ne_zero).mp h0
      have hmnc : IsCoprime m nn := Int.isCoprime_iff_gcd_eq_one.mpr hmn
      obtain ⟨p, hp⟩ := Int.sq_of_isCoprime (c := y) hmnc hymn
      obtain ⟨q, hq⟩ := Int.sq_of_isCoprime (c := y) hmnc.symm (by linear_combination hymn)
      have hp2 : m ^ 2 = p ^ 4 := by
        rcases hp with h | h <;> rw [h] <;> ring
      have hq2 : nn ^ 2 = q ^ 4 := by
        rcases hq with h | h <;> rw [h] <;> ring
      have hp0 : p ≠ 0 := by
        rintro rfl
        apply hm0
        rcases hp with h | h <;> simp [h]
      have hq0 : q ≠ 0 := by
        rintro rfl
        apply hnn0
        rcases hq with h | h <;> simp [h]
      have hE1 : p ^ 4 - q ^ 4 = x ^ 2 := by linear_combination -hm1 - hp2 + hq2
      have habs : |z| = ((N + 1 : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs, hzN']
      have hsum : p ^ 4 + q ^ 4 = (N : ℤ) + 1 := by
        rw [← hp2, ← hq2, ← hm3, habs]
        simp
      have hq4 : 0 < q ^ 4 := Even.pow_pos (by decide) hq0
      have hpN : (p.natAbs : ℤ) ≤ N := by
        have h1 := natAbs_le_pow4 p hp0
        linarith
      exact H1 p q x (by exact_mod_cast hpN) hE1 hp0 hq0 hx
  · -- gcd of x and y is at least 2: reduce by the common factor
    have hg2 : 2 ≤ Int.gcd x y := by
      have h0 : Int.gcd x y ≠ 0 := fun h0 => hx ((Int.gcd_eq_zero_iff.mp h0).1)
      omega
    obtain ⟨x', hx'⟩ := Int.gcd_dvd_left (a := x) (b := y)
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right (a := x) (b := y)
    have hx'0 : x' ≠ 0 := by
      rintro rfl
      apply hx
      rw [hx']
      ring
    have hy'0 : y' ≠ 0 := by
      rintro rfl
      apply hy
      rw [hy']
      ring
    exact E2_gcd N H2 (Int.gcd x y) x' y' z hg2 (by rw [← hx', ← hy']; exact hE) hx'0 hy'0 hz hzN'

theorem step1 (N : ℕ)
    (H1 : ∀ a b c : ℤ, a.natAbs ≤ N → a ^ 4 - b ^ 4 = c ^ 2 → a ≠ 0 → b ≠ 0 → c ≠ 0 → False)
    (H2 : ∀ x y z : ℤ, z.natAbs ≤ N + 1 → x ^ 4 + 4 * y ^ 4 = z ^ 2 → x ≠ 0 → y ≠ 0 → z ≠ 0 → False) :
    ∀ a b c : ℤ, a.natAbs ≤ N + 1 → a ^ 4 - b ^ 4 = c ^ 2 → a ≠ 0 → b ≠ 0 → c ≠ 0 → False := by
  intro a b c haN hE ha hb hc
  by_cases hsmall : a.natAbs ≤ N
  · exact H1 a b c hsmall hE ha hb hc
  have haN' : a.natAbs = N + 1 := by omega
  by_cases hg : Int.gcd a b = 1
  · have hcop : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hg
    have hbc : IsCoprime b c := by
      have h1 : IsCoprime b (a ^ 4) := hcop.symm.pow_right
      have h2 : IsCoprime b (a ^ 4 + b * (-(b ^ 3))) := h1.add_mul_left_right (-(b ^ 3))
      have h3 : c * c = a ^ 4 + b * (-(b ^ 3)) := by linear_combination -hE
      rw [← h3] at h2
      exact h2.of_mul_right_left
    have hbc' : IsCoprime b c := hbc
    rcases Int.even_or_odd b with hbe | hbo
    · -- b even, so c is odd; the triple (c, b², a²) gives b² = 2mn, c = m² − n²
      obtain ⟨b2, hb2⟩ := hbe
      have hco : c % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one c with h0 | h1
        · exfalso
          obtain ⟨c2, hc2⟩ : ∃ c2, c = c2 + c2 := ⟨c / 2, by omega⟩
          obtain ⟨u, v, huv⟩ := hbc
          rw [hb2, hc2] at huv
          have h2 : (2 : ℤ) * (u * b2 + v * c2) = 1 := by linear_combination huv
          generalize u * b2 + v * c2 = t at h2
          omega
        · exact h1
      have htriB : PythagoreanTriple c (b ^ 2) (a ^ 2) := by
        unfold PythagoreanTriple
        linear_combination -hE
      have hgcdB : Int.gcd c (b ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hbc'.symm.pow_right
      obtain ⟨m, nn, _, hB2, hB3, hB4, hB5, _⟩ :=
        PythagoreanTriple.coprime_classification' htriB hgcdB hco
          (lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha)))
      have hbb : b ^ 2 = 4 * b2 ^ 2 := by rw [hb2]; ring
      have hmn2 : m * nn = 2 * b2 ^ 2 := by
        have h2 : 2 * (m * nn) = 2 * (2 * b2 ^ 2) := by linear_combination hbb - hB2
        linarith
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hb
        have h0 : b2 ^ 2 = 0 := by linarith
        have hb20 : b2 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
        simp [hb2, hb20]
      have hnn0 : nn ≠ 0 := by
        rintro rfl
        apply hb
        have h0 : b2 ^ 2 = 0 := by linarith
        have hb20 : b2 = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
        simp [hb2, hb20]
      have hmc : IsCoprime m nn := Int.isCoprime_iff_gcd_eq_one.mpr hB4
      rcases hB5 with ⟨hm2, _⟩ | ⟨hm2, _⟩
      · -- m even: m = 2k, and k·nn = b2²
        obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
        have hkn : k * nn = b2 ^ 2 := by
          have h2 : 2 * (k * nn) = 2 * b2 ^ 2 := by
            rw [hk] at hmn2
            linear_combination hmn2
          linarith
        have hk0 : k ≠ 0 := by
          rintro rfl
          apply hm0
          rw [hk]
          ring
        have hkc : IsCoprime k nn := by
          rw [hk] at hmc
          exact hmc.of_mul_left_right
        have he : (2 * k) ^ 2 + nn ^ 2 = a ^ 2 := by
          rw [← hk]
          linear_combination -hB3
        obtain ⟨x2, y2, hx2, hy2, hE2⟩ := e2_from k nn b2 a hkc hkn hk0 hnn0 he
        exact H2 x2 y2 a haN'.le hE2 hx2 hy2 ha
      · -- nn even: nn = 2k, and k·m = b2²
        obtain ⟨k, hk⟩ : ∃ k, nn = 2 * k := ⟨nn / 2, by omega⟩
        have hkm : k * m = b2 ^ 2 := by
          have h2 : 2 * (k * m) = 2 * b2 ^ 2 := by
            rw [hk] at hmn2
            linear_combination hmn2
          linarith
        have hk0 : k ≠ 0 := by
          rintro rfl
          apply hnn0
          rw [hk]
          ring
        have hkc : IsCoprime k m := by
          rw [hk] at hmc
          exact hmc.of_mul_right_right.symm
        have he : (2 * k) ^ 2 + m ^ 2 = a ^ 2 := by
          rw [← hk]
          linear_combination -hB3
        obtain ⟨x2, y2, hx2, hy2, hE2⟩ := e2_from k m b2 a hkc hkm hk0 hm0 he
        exact H2 x2 y2 a haN'.le hE2 hx2 hy2 ha
    · -- b odd: the triple (b², c, a²) gives a smaller E1 solution (m, nn, ab)
      have htriA : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
        unfold PythagoreanTriple
        linear_combination -hE
      have hgcdA : Int.gcd (b ^ 2) c = 1 := Int.isCoprime_iff_gcd_eq_one.mp hbc'.pow_left
      obtain ⟨m, nn, hA1, hA2, hA3, _, _, _⟩ :=
        PythagoreanTriple.coprime_classification' htriA hgcdA (Int.odd_iff.mp hbo.pow)
          (lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha)))
      have hm0 : m ≠ 0 := by
        rintro rfl
        apply hc
        rw [hA2]
        ring
      have hnn0 : nn ≠ 0 := by
        rintro rfl
        apply hc
        rw [hA2]
        ring
      have hE' : m ^ 4 - nn ^ 4 = (a * b) ^ 2 := by
        linear_combination (-(m ^ 2 + nn ^ 2)) * hA1 - b ^ 2 * hA3
      have hsq : m ^ 2 < a ^ 2 := by
        have : 0 < nn ^ 2 := lt_of_le_of_ne (sq_nonneg nn) (Ne.symm (pow_ne_zero 2 hnn0))
        linarith
      have habs : |m| < |a| := sq_lt_sq.mp hsq
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at habs
      have hmN : m.natAbs ≤ N := by
        have : m.natAbs < a.natAbs := by exact_mod_cast habs
        omega
      exact H1 m nn (a * b) hmN hE' hm0 hnn0 (mul_ne_zero ha hb)
  · -- gcd of a and b is at least 2: reduce by the common factor
    have hg2 : 2 ≤ Int.gcd a b := by
      have h0 : Int.gcd a b ≠ 0 := fun h0 => ha ((Int.gcd_eq_zero_iff.mp h0).1)
      omega
    obtain ⟨a', ha'⟩ := Int.gcd_dvd_left (a := a) (b := b)
    obtain ⟨b', hb'⟩ := Int.gcd_dvd_right (a := a) (b := b)
    have ha'0 : a' ≠ 0 := by
      rintro rfl
      apply ha
      rw [ha']
      ring
    have hb'0 : b' ≠ 0 := by
      rintro rfl
      apply hb
      rw [hb']
      ring
    exact E1_gcd N H1 (Int.gcd a b) a' b' c hg2 (by rw [← ha', ← hb']; exact hE) ha'0 hb'0 hc
      (by rw [← ha']; exact haN')

theorem levels (N : ℕ) :
    (∀ a b c : ℤ, a.natAbs ≤ N → a ^ 4 - b ^ 4 = c ^ 2 → a ≠ 0 → b ≠ 0 → c ≠ 0 → False) ∧
    (∀ x y z : ℤ, z.natAbs ≤ N → x ^ 4 + 4 * y ^ 4 = z ^ 2 → x ≠ 0 → y ≠ 0 → z ≠ 0 → False) := by
  induction N with
  | zero =>
    refine ⟨fun a b c h _ ha _ _ => ha (Int.natAbs_eq_zero.mp (Nat.le_zero.mp h)),
      fun x y z h _ _ _ hz => hz (Int.natAbs_eq_zero.mp (Nat.le_zero.mp h))⟩
  | succ N ih =>
    have h2 := step2 N ih.1 ih.2
    exact ⟨step1 N ih.1 h2, h2⟩

theorem main : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro a b c ha hb hc h
  exact (levels a.natAbs).1 a b c le_rfl h ha hb hc

end MPP.Solutions.Bsd012
