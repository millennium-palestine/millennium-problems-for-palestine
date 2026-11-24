import Mathlib
import MPP.Solutions.Bsd040
import MPP.Solutions.Bsd059

namespace MPP.Solutions.Bsd073

theorem main : ∀ (e p : ℤ), 3 * e ^ 2 + p ≠ 0 →
    ∃ D : Finset ℤ, ∀ (x y : ℚ), y ^ 2 = x ^ 3 + (p : ℚ) * x + (-(e : ℚ) ^ 3 - (p : ℚ) * e) →
      x ≠ (e : ℚ) → ∃ d ∈ D, ∃ u : ℚ, x - (e : ℚ) = (d : ℚ) * u ^ 2 := by
  intro e p hR
  have hfin := MPP.Solutions.Bsd040.main (3 * e ^ 2 + p).natAbs.primeFactors
  refine ⟨hfin.toFinset, ?_⟩
  intro x y hy hx
  obtain ⟨r, hr⟩ := MPP.Solutions.Bsd059.main p (-(e ^ 3) - p * e) x y (by push_cast; exact hy)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.den_nz (by rw [hr]; ring)
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  -- the numerator of x is x · r²
  have hnum : (x.num : ℚ) = x * (r : ℚ) ^ 2 := by
    have h1 := Rat.num_div_den x
    rw [hr] at h1
    push_cast at h1
    exact (div_eq_iff (pow_ne_zero 2 hrQ)).mp h1
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = x.num := ⟨_, rfl⟩
  have hnum' : (n : ℚ) = x * (r : ℚ) ^ 2 := by rw [hn]; exact hnum
  have hcop : IsCoprime n (r : ℤ) := by
    have h1 := x.reduced
    rw [hr] at h1
    have h2 : Nat.Coprime x.num.natAbs r :=
      Nat.Coprime.coprime_dvd_right (dvd_pow_self r two_ne_zero) h1
    rw [hn, Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.Coprime] using h2
  -- x − e = A / r² and x² + e x + e² + p = Q / r⁴
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = n - e * (r : ℤ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = n ^ 2 + e * n * (r : ℤ) ^ 2 + (e ^ 2 + p) * (r : ℤ) ^ 4 :=
    ⟨_, rfl⟩
  have hAq : (A : ℚ) = (x - e) * (r : ℚ) ^ 2 := by
    rw [hA]; push_cast; rw [hnum']; ring
  have hQq : (Q : ℚ) = (x ^ 2 + e * x + (e ^ 2 + p)) * (r : ℚ) ^ 4 := by
    rw [hQ]; push_cast; rw [hnum']; ring
  -- A · Q is the square of y r³
  have hprod : ((A * Q : ℤ) : ℚ) = (y * (r : ℚ) ^ 3) ^ 2 := by
    push_cast
    rw [hAq, hQq]
    linear_combination (-(r : ℚ) ^ 6) * hy
  obtain ⟨s, hs⟩ : ∃ s : ℤ, (s : ℚ) = y * (r : ℚ) ^ 3 := by
    have hden : ((y * (r : ℚ) ^ 3) ^ 2).den = 1 := by
      rw [← hprod]
      exact Rat.den_intCast _
    rw [Rat.den_pow] at hden
    have hden1 : (y * (r : ℚ) ^ 3).den = 1 := by simpa using hden
    exact ⟨(y * (r : ℚ) ^ 3).num, Rat.coe_int_num_of_den_eq_one hden1⟩
  have hsZ : A * Q = s ^ 2 := by
    have : ((A * Q : ℤ) : ℚ) = ((s ^ 2 : ℤ) : ℚ) := by
      rw [hprod, ← hs]
      push_cast
      ring
    exact_mod_cast this
  have hA0 : A ≠ 0 := by
    intro h0
    apply hx
    have h1 : (x - e) * (r : ℚ) ^ 2 = 0 := by rw [← hAq, h0]; simp
    have h2 := (mul_eq_zero.mp h1).resolve_right (pow_ne_zero 2 hrQ)
    linarith
  -- squarefree part of A
  obtain ⟨a, b, hab, hsq⟩ := Nat.sq_mul_squarefree A.natAbs
  obtain ⟨d, hdA, hdsq⟩ : ∃ d : ℤ, A = d * (b : ℤ) ^ 2 ∧ Squarefree d.natAbs := by
    rcases Int.natAbs_eq A with h | h
    · exact ⟨a, by rw [h, ← hab]; push_cast; ring, by simpa using hsq⟩
    · exact ⟨-(a : ℤ), by rw [h, ← hab]; push_cast; ring, by simpa using hsq⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hA0 (by rw [hdA]; ring)
  have hb0 : (b : ℤ) ≠ 0 := by
    intro h0
    apply hA0
    rw [hdA]
    have : (b : ℤ) = 0 := h0
    rw [this]
    ring
  -- every prime of d divides 3e² + p
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ d → ℓ ∈ (3 * e ^ 2 + p).natAbs.primeFactors := by
    intro ℓ hℓ hℓd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    apply Nat.mem_primeFactors.mpr
    refine ⟨hℓ, ?_, Int.natAbs_ne_zero.mpr hR⟩
    apply Int.ofNat_dvd_left.mp
    by_contra hcon
    have hpℓ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
    have hdAℓ : (ℓ : ℤ) ∣ A := by
      rw [hdA]
      exact Dvd.dvd.mul_right hℓd _
    -- ℓ does not divide r
    have hnr : ¬ (ℓ : ℤ) ∣ (r : ℤ) := by
      intro hr'
      have hn' : (ℓ : ℤ) ∣ n := by
        have hn_eq : n = A + e * (r : ℤ) ^ 2 := by rw [hA]; ring
        rw [hn_eq]
        exact dvd_add hdAℓ (Dvd.dvd.mul_left (dvd_pow hr' two_ne_zero) _)
      exact hpℓ.not_unit (hcop.isUnit_of_dvd' hn' hr')
    -- ℓ does not divide Q
    have hnQ : ¬ (ℓ : ℤ) ∣ Q := by
      intro hQd
      have hid : Q = (3 * e ^ 2 + p) * (r : ℤ) ^ 4 + A * (n + 2 * e * (r : ℤ) ^ 2) := by
        rw [hQ, hA]; ring
      have h1 : (ℓ : ℤ) ∣ (3 * e ^ 2 + p) * (r : ℤ) ^ 4 := by
        have h2 : (3 * e ^ 2 + p) * (r : ℤ) ^ 4 = Q - A * (n + 2 * e * (r : ℤ) ^ 2) := by
          rw [hid]; ring
        rw [h2]
        exact dvd_sub hQd (Dvd.dvd.mul_right hdAℓ _)
      rcases hpℓ.dvd_or_dvd h1 with h2 | h2
      · exact hcon h2
      · exact hnr (hpℓ.dvd_of_dvd_pow h2)
    -- valuations at ℓ: v(A) = v(s²) − v(Q) is even, but v(A) = 1 + 2 v(b) is odd
    have hQ0 : Q ≠ 0 := fun h0 => hnQ (by rw [h0]; exact dvd_zero _)
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0] at hsZ
      have : A * Q = 0 := by simpa using hsZ
      exact mul_ne_zero hA0 hQ0 this
    have hv1 : padicValInt ℓ (A * Q) = padicValInt ℓ A + padicValInt ℓ Q :=
      padicValInt.mul hA0 hQ0
    have hv2 : padicValInt ℓ Q = 0 := padicValInt.eq_zero_of_not_dvd hnQ
    have hv3 : padicValInt ℓ (s ^ 2) = 2 * padicValInt ℓ s := by
      rw [sq, padicValInt.mul hs0 hs0]
      ring
    have hv4 : padicValInt ℓ A = padicValInt ℓ d + 2 * padicValInt ℓ (b : ℤ) := by
      rw [hdA, padicValInt.mul hd0 (pow_ne_zero 2 hb0), sq, padicValInt.mul hb0 hb0]
      ring
    have hd1 : padicValInt ℓ d = 1 := by
      have hdn : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
      have hle : d.natAbs.factorization ℓ ≤ 1 := hdsq.natFactorization_le_one ℓ
      have hge : 1 ≤ d.natAbs.factorization ℓ :=
        (hℓ.dvd_iff_one_le_factorization hdn).mp (Int.natCast_dvd.mp hℓd)
      rw [padicValInt, ← Nat.factorization_def _ hℓ]
      omega
    rw [hsZ] at hv1
    omega
  refine ⟨d, hfin.mem_toFinset.mpr ⟨hdsq, hprime⟩, (b : ℚ) / (r : ℚ), ?_⟩
  have hAd : (A : ℚ) = (d : ℚ) * (b : ℚ) ^ 2 := by
    rw [hdA]; push_cast; ring
  rw [hAq] at hAd
  rw [div_pow]
  field_simp
  linear_combination hAd

end MPP.Solutions.Bsd073
