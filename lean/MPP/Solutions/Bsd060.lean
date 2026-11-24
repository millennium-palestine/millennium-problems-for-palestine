import Mathlib
import MPP.Solutions.Bsd040
import MPP.Solutions.Bsd058
import MPP.Solutions.Bsd059

namespace MPP.Solutions.Bsd060

theorem main : ∀ (e1 e2 e3 : ℤ), e1 + e2 + e3 = 0 → e1 ≠ e2 → e1 ≠ e3 → e2 ≠ e3 →
    ∃ D : Finset ℤ, ∀ (x y : ℚ), y ^ 2 = (x - e1) * (x - e2) * (x - e3) → x ≠ e1 →
      ∃ d ∈ D, ∃ u : ℚ, x - e1 = (d : ℚ) * u ^ 2 := by
  intro e1 e2 e3 hs h12 h13 h23
  have hD0 : (e1 - e2) * (e1 - e3) * (e2 - e3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)
  -- the primes dividing a root difference
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime →
      ((p : ℤ) ∣ (e1 - e2) ∨ (p : ℤ) ∣ (e1 - e3) ∨ (p : ℤ) ∣ (e2 - e3)) → p ∈ S := by
    refine ⟨((e1 - e2) * (e1 - e3) * (e2 - e3)).natAbs.primeFactors, ?_⟩
    intro p hp h
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Int.natAbs_ne_zero.mpr hD0⟩
    rw [← Int.ofNat_dvd_left]
    rcases h with h | h | h
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
    · exact Dvd.dvd.mul_left h _
  have hfin := MPP.Solutions.Bsd040.main S
  refine ⟨hfin.toFinset, ?_⟩
  intro x y hy hx
  -- Step 1: the denominator of x is a square
  have hf : (x - e1) * (x - e2) * (x - e3) =
      x ^ 3 + ((e1 * e2 + e1 * e3 + e2 * e3 : ℤ) : ℚ) * x + ((-(e1 * e2 * e3) : ℤ) : ℚ) := by
    have he3 : (e3 : ℚ) = -e1 - e2 := by
      have : e3 = -e1 - e2 := by linarith
      exact_mod_cast this
    push_cast
    rw [he3]
    ring
  obtain ⟨r, hr⟩ := MPP.Solutions.Bsd059.main (e1 * e2 + e1 * e3 + e2 * e3) (-(e1 * e2 * e3)) x y
    (hy.trans hf)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact x.den_nz (by rw [hr]; ring)
  have hrQ : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hnum : (x.num : ℚ) = x * (r : ℚ) ^ 2 := by
    have h1 := Rat.num_div_den x
    rw [hr] at h1
    have h2 := (div_eq_iff (Nat.cast_ne_zero.mpr (pow_ne_zero 2 hr0))).mp h1
    push_cast at h2
    exact h2
  have hcop : IsCoprime x.num (r : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 := x.reduced
    rw [hr] at h1
    have h2 : Nat.Coprime x.num.natAbs r :=
      Nat.Coprime.coprime_dvd_right (dvd_pow_self r two_ne_zero) h1
    simpa [Int.gcd, Nat.Coprime] using h2
  -- the three integers A, B, C = num(x) − e_i r²
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = x.num - e1 * (r : ℤ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = x.num - e2 * (r : ℤ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = x.num - e3 * (r : ℤ) ^ 2 := ⟨_, rfl⟩
  have hAq : (A : ℚ) = (r : ℚ) ^ 2 * (x - e1) := by
    rw [hA]
    push_cast
    rw [hnum]
    ring
  have hBq : (B : ℚ) = (r : ℚ) ^ 2 * (x - e2) := by
    rw [hB]
    push_cast
    rw [hnum]
    ring
  have hCq : (C : ℚ) = (r : ℚ) ^ 2 * (x - e3) := by
    rw [hC]
    push_cast
    rw [hnum]
    ring
  have hA0 : A ≠ 0 := by
    intro h0
    apply hx
    have h1 : (r : ℚ) ^ 2 * (x - e1) = 0 := by rw [← hAq, h0]; simp
    have h2 := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hrQ)
    linarith
  -- the product A B C is a square of y r³
  have hprod : ((A * B * C : ℤ) : ℚ) = (y * (r : ℚ) ^ 3) ^ 2 := by
    push_cast
    rw [hAq, hBq, hCq]
    have : (r : ℚ) ^ 2 * (x - e1) * ((r : ℚ) ^ 2 * (x - e2)) * ((r : ℚ) ^ 2 * (x - e3)) =
        (r : ℚ) ^ 6 * ((x - e1) * (x - e2) * (x - e3)) := by ring
    rw [this, ← hy]
    ring
  -- y r³ is an integer, since its square is
  obtain ⟨s, hs'⟩ : ∃ s : ℤ, (s : ℚ) = y * (r : ℚ) ^ 3 := by
    have hden : ((y * (r : ℚ) ^ 3) ^ 2).den = 1 := by
      rw [← hprod]
      exact Rat.den_intCast _
    rw [Rat.den_pow] at hden
    have hden1 : (y * (r : ℚ) ^ 3).den = 1 := by
      simpa using hden
    exact ⟨(y * (r : ℚ) ^ 3).num, Rat.coe_int_num_of_den_eq_one hden1⟩
  have hsZ : A * B * C = s ^ 2 := by
    have : ((A * B * C : ℤ) : ℚ) = ((s ^ 2 : ℤ) : ℚ) := by
      rw [hprod]
      push_cast
      rw [hs']
    exact_mod_cast this
  have hprod58 : (x.num - e1 * (r : ℤ) ^ 2) * (x.num - e2 * (r : ℤ) ^ 2) *
      (x.num - e3 * (r : ℤ) ^ 2) = s ^ 2 := by
    rw [← hA, ← hB, ← hC]
    exact hsZ
  -- the squarefree part of A
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
  -- every prime factor of d lies in S
  have hprime : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ S := by
    intro p hp hpd
    apply hS p hp
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    haveI : Fact p.Prime := ⟨hp⟩
    have hpA : (p : ℤ) ∣ A := by
      rw [hdA]
      exact Dvd.dvd.mul_right hpd _
    have hAr : IsCoprime A (r : ℤ) := by
      rw [hA]
      have e : x.num - e1 * (r : ℤ) ^ 2 = x.num + (r : ℤ) * (-(e1 * (r : ℤ))) := by ring
      rw [e]
      exact hcop.add_mul_left_left _
    have hpr : ¬ (p : ℤ) ∣ (r : ℤ) := by
      intro hpr
      have hu := hAr.isUnit_of_dvd' hpA hpr
      exact (Nat.prime_iff_prime_int.mp hp).not_unit hu
    have hgcd : Int.gcd x.num (r : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    obtain ⟨hev, -, -⟩ := MPP.Solutions.Bsd058.main x.num (r : ℤ) s e1 e2 e3 p hp hgcd h1 h2 h3 hprod58
    rw [← hA] at hev
    have hv : padicValInt p A = padicValInt p d + 2 * padicValInt p (b : ℤ) := by
      rw [hdA, padicValInt.mul hd0 (pow_ne_zero 2 hb0), sq, padicValInt.mul hb0 hb0]
      ring
    have hd1 : padicValInt p d = 1 := by
      have hdn : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
      have hle : d.natAbs.factorization p ≤ 1 := hdsq.natFactorization_le_one p
      have hge : 1 ≤ d.natAbs.factorization p :=
        (hp.dvd_iff_one_le_factorization hdn).mp (Int.natCast_dvd.mp hpd)
      rw [padicValInt, ← Nat.factorization_def _ hp]
      omega
    obtain ⟨k, hk⟩ := hev
    rw [hv, hd1] at hk
    omega
  refine ⟨d, hfin.mem_toFinset.mpr ⟨hdsq, hprime⟩, (b : ℚ) / (r : ℚ), ?_⟩
  have hq : x - (e1 : ℚ) = (A : ℚ) / (r : ℚ) ^ 2 := by
    rw [hAq]
    field_simp
  rw [hq, hdA]
  push_cast
  ring

end MPP.Solutions.Bsd060
