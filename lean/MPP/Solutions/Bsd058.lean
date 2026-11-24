import Mathlib

namespace MPP.Solutions.Bsd058

theorem main : ∀ (u v s e1 e2 e3 : ℤ) (ℓ : ℕ), Nat.Prime ℓ → Int.gcd u v = 1 →
    ¬ (ℓ : ℤ) ∣ (e1 - e2) → ¬ (ℓ : ℤ) ∣ (e1 - e3) → ¬ (ℓ : ℤ) ∣ (e2 - e3) →
    (u - e1 * v ^ 2) * (u - e2 * v ^ 2) * (u - e3 * v ^ 2) = s ^ 2 →
      Even (padicValInt ℓ (u - e1 * v ^ 2)) ∧ Even (padicValInt ℓ (u - e2 * v ^ 2)) ∧
        Even (padicValInt ℓ (u - e3 * v ^ 2)) := by
  intro u v s e1 e2 e3 ℓ hℓ hg h12 h13 h23 hprod
  haveI : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
  have hP : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  -- a prime dividing both u and v contradicts gcd(u, v) = 1
  have hfin : (ℓ : ℤ) ∣ u → (ℓ : ℤ) ∣ v → False := by
    intro h1 h2
    obtain ⟨a, b, hab⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hg
    have h4 : (ℓ : ℤ) ∣ a * u + b * v := dvd_add (dvd_mul_of_dvd_right h1 a) (dvd_mul_of_dvd_right h2 b)
    rw [hab] at h4
    exact hP.not_dvd_one h4
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = u - e1 * v ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = u - e2 * v ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = u - e3 * v ^ 2 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hC] at hprod
  rw [← hA, ← hB, ← hC]
  -- ℓ divides at most one of A, B, C
  have hAB : ¬ ((ℓ : ℤ) ∣ A ∧ (ℓ : ℤ) ∣ B) := by
    rintro ⟨hA', hB'⟩
    have e : B - A = (e1 - e2) * v ^ 2 := by rw [hA, hB]; ring
    have h1 : (ℓ : ℤ) ∣ (e1 - e2) * v ^ 2 := by rw [← e]; exact dvd_sub hB' hA'
    have h2 : (ℓ : ℤ) ∣ v := by
      rcases hP.dvd_or_dvd h1 with h | h
      · exact absurd h h12
      · exact hP.dvd_of_dvd_pow h
    have h3 : (ℓ : ℤ) ∣ u := by
      have e' : u = A + e1 * v ^ 2 := by rw [hA]; ring
      rw [e']
      exact dvd_add hA' (dvd_mul_of_dvd_right (dvd_pow h2 two_ne_zero) _)
    exact hfin h3 h2
  have hAC : ¬ ((ℓ : ℤ) ∣ A ∧ (ℓ : ℤ) ∣ C) := by
    rintro ⟨hA', hC'⟩
    have e : C - A = (e1 - e3) * v ^ 2 := by rw [hA, hC]; ring
    have h1 : (ℓ : ℤ) ∣ (e1 - e3) * v ^ 2 := by rw [← e]; exact dvd_sub hC' hA'
    have h2 : (ℓ : ℤ) ∣ v := by
      rcases hP.dvd_or_dvd h1 with h | h
      · exact absurd h h13
      · exact hP.dvd_of_dvd_pow h
    have h3 : (ℓ : ℤ) ∣ u := by
      have e' : u = A + e1 * v ^ 2 := by rw [hA]; ring
      rw [e']
      exact dvd_add hA' (dvd_mul_of_dvd_right (dvd_pow h2 two_ne_zero) _)
    exact hfin h3 h2
  have hBC : ¬ ((ℓ : ℤ) ∣ B ∧ (ℓ : ℤ) ∣ C) := by
    rintro ⟨hB', hC'⟩
    have e : C - B = (e2 - e3) * v ^ 2 := by rw [hB, hC]; ring
    have h1 : (ℓ : ℤ) ∣ (e2 - e3) * v ^ 2 := by rw [← e]; exact dvd_sub hC' hB'
    have h2 : (ℓ : ℤ) ∣ v := by
      rcases hP.dvd_or_dvd h1 with h | h
      · exact absurd h h23
      · exact hP.dvd_of_dvd_pow h
    have h3 : (ℓ : ℤ) ∣ u := by
      have e' : u = B + e2 * v ^ 2 := by rw [hB]; ring
      rw [e']
      exact dvd_add hB' (dvd_mul_of_dvd_right (dvd_pow h2 two_ne_zero) _)
    exact hfin h3 h2
  -- if ℓ divides X and not Y, Z, then the valuation of X is twice that of s
  have hgen : ∀ X Y Z : ℤ, X * Y * Z = s ^ 2 → (ℓ : ℤ) ∣ X → ¬ (ℓ : ℤ) ∣ Y → ¬ (ℓ : ℤ) ∣ Z →
      Even (padicValInt ℓ X) := by
    intro X Y Z hXYZ hX hY hZ
    by_cases hX0 : X = 0
    · simp [hX0]
    have hY0 : Y ≠ 0 := by
      rintro rfl
      exact hY (dvd_zero _)
    have hZ0 : Z ≠ 0 := by
      rintro rfl
      exact hZ (dvd_zero _)
    have hne : X * Y * Z ≠ 0 := mul_ne_zero (mul_ne_zero hX0 hY0) hZ0
    have hs : s ≠ 0 := by
      intro h0
      apply hne
      rw [hXYZ, h0]
      ring
    have hvY : padicValInt ℓ Y = 0 := padicValInt.eq_zero_of_not_dvd hY
    have hvZ : padicValInt ℓ Z = 0 := padicValInt.eq_zero_of_not_dvd hZ
    have hmul : padicValInt ℓ (X * Y * Z) = padicValInt ℓ X + padicValInt ℓ Y + padicValInt ℓ Z := by
      rw [padicValInt.mul (mul_ne_zero hX0 hY0) hZ0, padicValInt.mul hX0 hY0]
    have hsq : padicValInt ℓ (s ^ 2) = padicValInt ℓ s + padicValInt ℓ s := by
      rw [pow_two, padicValInt.mul hs hs]
    rw [hXYZ, hsq, hvY, hvZ] at hmul
    exact ⟨padicValInt ℓ s, by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases hA' : (ℓ : ℤ) ∣ A
    · exact hgen A B C hprod hA' (fun hb => hAB ⟨hA', hb⟩) (fun hc => hAC ⟨hA', hc⟩)
    · rw [padicValInt.eq_zero_of_not_dvd hA']
      exact ⟨0, rfl⟩
  · by_cases hB' : (ℓ : ℤ) ∣ B
    · exact hgen B A C (by rw [← hprod]; ring) hB' (fun ha => hAB ⟨ha, hB'⟩)
        (fun hc => hBC ⟨hB', hc⟩)
    · rw [padicValInt.eq_zero_of_not_dvd hB']
      exact ⟨0, rfl⟩
  · by_cases hC' : (ℓ : ℤ) ∣ C
    · exact hgen C A B (by rw [← hprod]; ring) hC' (fun ha => hAC ⟨ha, hC'⟩)
        (fun hb => hBC ⟨hb, hC'⟩)
    · rw [padicValInt.eq_zero_of_not_dvd hC']
      exact ⟨0, rfl⟩

end MPP.Solutions.Bsd058
