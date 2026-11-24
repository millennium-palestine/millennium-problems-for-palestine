import Mathlib
import MPP.Solutions.Bsd037

namespace MPP.Solutions.Bsd043

-- A binary cubic with coefficients c₀ … c₃ is bounded by the sum of the coefficient sizes times M³.
lemma cubic_abs_le (c0 c1 c2 c3 a d M : ℤ) (ha : |a| ≤ M) (hd : |d| ≤ M) (hM : 0 ≤ M) :
    |c0 * a ^ 3 + c1 * a ^ 2 * d + c2 * a * d ^ 2 + c3 * d ^ 3| ≤
      (|c0| + |c1| + |c2| + |c3|) * M ^ 3 := by
  have m0 : |a ^ 3| ≤ M ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg a) ha 3
  have m1 : |a ^ 2 * d| ≤ M ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |a| ^ 2 * |d| ≤ M ^ 2 * M :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg a) ha 2) hd (abs_nonneg _) (by positivity)
      _ = M ^ 3 := by ring
  have m2 : |a * d ^ 2| ≤ M ^ 3 := by
    rw [abs_mul, abs_pow]
    calc |a| * |d| ^ 2 ≤ M * M ^ 2 :=
          mul_le_mul ha (pow_le_pow_left₀ (abs_nonneg d) hd 2) (by positivity) hM
      _ = M ^ 3 := by ring
  have m3 : |d ^ 3| ≤ M ^ 3 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg d) hd 3
  have t0 : |c0 * a ^ 3| ≤ |c0| * M ^ 3 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left m0 (abs_nonneg _)
  have t1 : |c1 * (a ^ 2 * d)| ≤ |c1| * M ^ 3 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left m1 (abs_nonneg _)
  have t2 : |c2 * (a * d ^ 2)| ≤ |c2| * M ^ 3 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left m2 (abs_nonneg _)
  have t3 : |c3 * d ^ 3| ≤ |c3| * M ^ 3 := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left m3 (abs_nonneg _)
  have split : c0 * a ^ 3 + c1 * a ^ 2 * d + c2 * a * d ^ 2 + c3 * d ^ 3 =
      c0 * a ^ 3 + c1 * (a ^ 2 * d) + c2 * (a * d ^ 2) + c3 * d ^ 3 := by ring
  rw [split]
  have tri := abs_add_le (c0 * a ^ 3 + c1 * (a ^ 2 * d) + c2 * (a * d ^ 2)) (c3 * d ^ 3)
  have tri3 := abs_add_three (c0 * a ^ 3) (c1 * (a ^ 2 * d)) (c2 * (a * d ^ 2))
  have expand : (|c0| + |c1| + |c2| + |c3|) * M ^ 3 =
      |c0| * M ^ 3 + |c1| * M ^ 3 + |c2| * M ^ 3 + |c3| * M ^ 3 := by ring
  rw [expand]
  linarith

lemma sum_bound (SA SV SD SE P S : ℤ) (hA : 0 ≤ SA) (hV : 0 ≤ SV) (hD : 0 ≤ SD + SE)
    (hP : 0 ≤ P) (hS : 0 ≤ S) :
    SA * P * S + SV * P * S ≤ (1 + (SA + SV) + (SD + SE)) * P * S := by
  have h1 : 0 ≤ (SD + SE) * (P * S) := mul_nonneg hD (mul_nonneg hP hS)
  have h2 : 0 ≤ P * S := mul_nonneg hP hS
  nlinarith

lemma sum_bound_d (SA SV SD SE P S : ℤ) (hA : 0 ≤ SA + SV) (hD : 0 ≤ SD) (hE : 0 ≤ SE)
    (hP : 0 ≤ P) (hS : 0 ≤ S) :
    SD * P * S + SE * P * S ≤ (1 + (SA + SV) + (SD + SE)) * P * S := by
  have h1 : 0 ≤ (SA + SV) * (P * S) := mul_nonneg hA (mul_nonneg hP hS)
  have h2 : 0 ≤ P * S := mul_nonneg hP hS
  nlinarith

-- The two integral doubling identities: U n + V δ = Q l⁸ a⁷ and the same with d⁷,
-- where n = l⁴ F(a,d) and δ = l⁴ D(a,d) for the doubling formula of y² = x³ + … .
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
lemma coeff_ident (l B2 B4 B6 B8 : ℤ) :
    ∃ ua0 ua1 ua2 ua3 va0 va1 va2 va3 ud0 ud1 ud2 ud3 ve0 ve1 ve2 ve3 : ℤ,
      (∀ a d : ℤ, (ua0 * a ^ 3 + ua1 * a ^ 2 * d + ua2 * a * d ^ 2 + ua3 * d ^ 3) * (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) + (va0 * a ^ 3 + va1 * a ^ 2 * d + va2 * a * d ^ 2 + va3 * d ^ 3) * (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) = (B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) * l ^ 8 * a ^ 7) ∧
      (∀ a d : ℤ, (ud0 * a ^ 3 + ud1 * a ^ 2 * d + ud2 * a * d ^ 2 + ud3 * d ^ 3) * (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) + (ve0 * a ^ 3 + ve1 * a ^ 2 * d + ve2 * a * d ^ 2 + ve3 * d ^ 3) * (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) = (B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) * l ^ 8 * d ^ 7) := by
  refine ⟨(B2^4*B8^2*l^4 - 6*B2^3*B4*B6*B8*l^4 + 4*B2^3*B6^3*l^4 + 4*B2^2*B4^3*B8*l^4 - 3*B2^2*B4^2*B6^2*l^4 - 48*B2^2*B4*B8^2*l^4 + 6*B2^2*B6^2*B8*l^4 + 240*B2*B4^2*B6*B8*l^4 - 162*B2*B4*B6^3*l^4 + 192*B2*B6*B8^2*l^4 - 144*B4^4*B8*l^4 + 108*B4^3*B6^2*l^4 + 384*B4^2*B8^2*l^4 - 1296*B4*B6^2*B8*l^4 + 729*B6^4*l^4 - 256*B8^3*l^4), (-4*B2^3*B4*B8^2*l^3 + 24*B2^2*B4^2*B6*B8*l^3 - 16*B2^2*B4*B6^3*l^3 + 36*B2^2*B6*B8^2*l^3 - 16*B2*B4^4*B8*l^3 + 12*B2*B4^3*B6^2*l^3 + 48*B2*B4^2*B8^2*l^3 - 240*B2*B4*B6^2*B8*l^3 + 144*B2*B6^4*l^3 - 64*B2*B8^3*l^3 + 48*B4^3*B6*B8*l^3 - 36*B4^2*B6^3*l^3 + 64*B4*B6*B8^2*l^3 - 36*B6^3*B8*l^3), (B2^3*B6*B8^2*l^2 - 12*B2^2*B4^2*B8^2*l^2 - 6*B2^2*B4*B6^2*B8*l^2 + 4*B2^2*B6^4*l^2 + 76*B2*B4^3*B6*B8*l^2 - 51*B2*B4^2*B6^3*l^2 + 64*B2*B4*B6*B8^2*l^2 + 7*B2*B6^3*B8*l^2 - 48*B4^5*B8*l^2 + 36*B4^4*B6^2*l^2 + 160*B4^3*B8^2*l^2 - 528*B4^2*B6^2*B8*l^2 + 297*B4*B6^4*l^2 - 128*B4*B8^3*l^2 + 16*B6^2*B8^2*l^2), (-6*B2^2*B4*B6*B8^2*l + 36*B2*B4^2*B6^2*B8*l - 24*B2*B4*B6^4*l + 40*B2*B6^2*B8^2*l - 24*B4^4*B6*B8*l + 18*B4^3*B6^3*l + 80*B4^2*B6*B8^2*l - 282*B4*B6^3*B8*l + 162*B6^5*l - 64*B6*B8^3*l), (B2^3*B4*B8^2*l^3 - 6*B2^2*B4^2*B6*B8*l^3 + 4*B2^2*B4*B6^3*l^3 - 9*B2^2*B6*B8^2*l^3 + 4*B2*B4^4*B8*l^3 - 3*B2*B4^3*B6^2*l^3 - 12*B2*B4^2*B8^2*l^3 + 60*B2*B4*B6^2*B8*l^3 - 36*B2*B6^4*l^3 + 16*B2*B8^3*l^3 - 12*B4^3*B6*B8*l^3 + 9*B4^2*B6^3*l^3 - 16*B4*B6*B8^2*l^3 + 9*B6^3*B8*l^3), (2*B2^3*B6*B8^2*l^2 - 6*B2^2*B4^2*B8^2*l^2 - 12*B2^2*B4*B6^2*B8*l^2 + 8*B2^2*B6^4*l^2 - 4*B2^2*B8^3*l^2 + 44*B2*B4^3*B6*B8*l^2 - 30*B2*B4^2*B6^3*l^2 + 36*B2*B4*B6*B8^2*l^2 - 4*B2*B6^3*B8*l^2 - 24*B4^5*B8*l^2 + 18*B4^4*B6^2*l^2 + 56*B4^3*B8^2*l^2 - 192*B4^2*B6^2*B8*l^2 + 108*B4*B6^4*l^2 - 32*B4*B8^3*l^2 - 4*B6^2*B8^2*l^2), (B2^3*B8^3*l - 18*B2^2*B4*B6*B8^2*l + 4*B2^2*B6^3*B8*l + 4*B2*B4^3*B8^2*l + 69*B2*B4^2*B6^2*B8*l - 48*B2*B4*B6^4*l - 16*B2*B4*B8^3*l + 87*B2*B6^2*B8^2*l - 48*B4^4*B6*B8*l + 36*B4^3*B6^3*l + 196*B4^2*B6*B8^2*l - 591*B4*B6^3*B8*l + 324*B6^5*l - 112*B6*B8^3*l), (-6*B2^2*B4*B8^3 + 36*B2*B4^2*B6*B8^2 - 24*B2*B4*B6^3*B8 + 40*B2*B6*B8^3 - 24*B4^4*B8^2 + 18*B4^3*B6^2*B8 + 80*B4^2*B8^3 - 282*B4*B6^2*B8^2 + 162*B6^4*B8 - 64*B8^4),
    (0), (8*B2^3*B6*l^10 - 8*B2^2*B4^2*l^10 + 16*B2^2*B8*l^10 - 336*B2*B4*B6*l^10 + 288*B4^3*l^10 - 384*B4*B8*l^10 + 1296*B6^2*l^10), (2*B2^4*B6*l^9 - 2*B2^3*B4^2*l^9 - 80*B2^2*B4*B6*l^9 + 72*B2*B4^3*l^9 + 32*B2*B4*B8*l^9 + 360*B2*B6^2*l^9 - 144*B4^2*B6*l^9 - 576*B6*B8*l^9), (-B2^4*B8*l^8 + 5*B2^3*B4*B6*l^8 - 4*B2^2*B4^3*l^8 + 48*B2^2*B4*B8*l^8 + B2^2*B6^2*l^8 - 204*B2*B4^2*B6*l^8 - 176*B2*B6*B8*l^8 + 144*B4^4*l^8 - 384*B4^2*B8*l^8 + 864*B4*B6^2*l^8 + 256*B8^2*l^8), (-2*B2^3*B6*l^10 + 2*B2^2*B4^2*l^10 - 4*B2^2*B8*l^10 + 84*B2*B4*B6*l^10 - 72*B4^3*l^10 + 96*B4*B8*l^10 - 324*B6^2*l^10), (B2^3*B8*l^9 - B2^2*B4*B6*l^9 - 32*B2*B4*B8*l^9 - 9*B2*B6^2*l^9 + 36*B4^2*B6*l^9 + 144*B6*B8*l^9), (2*B2^3*B4*B6*l^8 - 2*B2^2*B4^3*l^8 + 2*B2^2*B4*B8*l^8 + 2*B2^2*B6^2*l^8 - 84*B2*B4^2*B6*l^8 + 8*B2*B6*B8*l^8 + 72*B4^4*l^8 - 48*B4^2*B8*l^8 + 270*B4*B6^2*l^8 - 64*B8^2*l^8), (-B2^3*B4*B8*l^7 + 4*B2^3*B6^2*l^7 - 3*B2^2*B4^2*B6*l^7 + 7*B2^2*B6*B8*l^7 + 36*B2*B4^2*B8*l^7 - 162*B2*B4*B6^2*l^7 + 16*B2*B8^2*l^7 + 108*B4^3*B6*l^7 - 432*B4*B6*B8*l^7 + 729*B6^3*l^7), ?_, ?_⟩
  · intro a d; ring
  · intro a d; ring

-- Core bound: for coprime integers a, d (d > 0) and integers p, q with p/q = N/Dz,
-- the reduced fraction has size at least M⁴ / K, and is controlled by the constant |Q l⁸|.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
lemma core_bound (l B2 B4 B6 B8 Q : ℤ) (hl : 0 < l) (hQ : Q ≠ 0)
    (ua0 ua1 ua2 ua3 va0 va1 va2 va3 ud0 ud1 ud2 ud3 ve0 ve1 ve2 ve3 : ℤ)
    (hU : ∀ a d : ℤ, (ua0 * a ^ 3 + ua1 * a ^ 2 * d + ua2 * a * d ^ 2 + ua3 * d ^ 3) * (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) + (va0 * a ^ 3 + va1 * a ^ 2 * d + va2 * a * d ^ 2 + va3 * d ^ 3) * (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) = Q * l ^ 8 * a ^ 7)
    (hV : ∀ a d : ℤ, (ud0 * a ^ 3 + ud1 * a ^ 2 * d + ud2 * a * d ^ 2 + ud3 * d ^ 3) * (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) + (ve0 * a ^ 3 + ve1 * a ^ 2 * d + ve2 * a * d ^ 2 + ve3 * d ^ 3) * (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) = Q * l ^ 8 * d ^ 7) :
    ∃ K : ℤ, 0 < K ∧ ∀ a d p q : ℤ, 0 < d → IsCoprime a d → 0 < q → IsCoprime p q →
      p * (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) = q * (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) →
      |Q * l ^ 8| * (max |a| d) ^ 4 ≤ K * max |(l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4)| |(d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3))| ∧
        max |(l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4)| |(d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3))| ≤ |Q * l ^ 8| * max |p| q := by
  refine ⟨1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) +
    (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|)), by positivity, ?_⟩
  intro a d p q hd hac hq hpq hrel
  have e1 := hU a d
  have e2 := hV a d
  set M := max |a| d with hMdef
  have hMa : |a| ≤ M := le_max_left _ _
  have hMd : |d| ≤ M := by rw [abs_of_pos hd]; exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg a) hMa
  have hMpos : 0 < M := lt_of_lt_of_le hd (le_max_right _ _)
  have hUa := cubic_abs_le ua0 ua1 ua2 ua3 a d M hMa hMd hM0
  have hVa := cubic_abs_le va0 va1 va2 va3 a d M hMa hMd hM0
  have hUd := cubic_abs_le ud0 ud1 ud2 ud3 a d M hMa hMd hM0
  have hVd := cubic_abs_le ve0 ve1 ve2 ve3 a d M hMa hMd hM0
  set N := (l^4 * a^4 - B4 * l^2 * a^2 * d^2 - 2 * B6 * l * a * d^3 - B8 * d^4) with hNdef
  set Dz := (d * (4 * l^4 * a^3 + B2 * l^3 * a^2 * d + 2 * B4 * l^2 * a * d^2 + B6 * l * d^3)) with hDdef
  set S := max |N| |Dz| with hSdef
  have hNS : |N| ≤ S := le_max_left _ _
  have hDS : |Dz| ≤ S := le_max_right _ _
  have hS0 : 0 ≤ S := le_trans (abs_nonneg N) hNS
  have hP3 : 0 ≤ M ^ 3 := pow_nonneg hM0 3
  have hA : |Q * l ^ 8| * |a| ^ 7 ≤ (1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) +
      (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * M ^ 3 * S := by
    have h1 : |Q * l ^ 8 * a ^ 7| = |Q * l ^ 8| * |a| ^ 7 := by rw [abs_mul, abs_pow]
    rw [← h1, ← e1]
    calc |(ua0 * a ^ 3 + ua1 * a ^ 2 * d + ua2 * a * d ^ 2 + ua3 * d ^ 3) * N + (va0 * a ^ 3 + va1 * a ^ 2 * d + va2 * a * d ^ 2 + va3 * d ^ 3) * Dz| ≤ |(ua0 * a ^ 3 + ua1 * a ^ 2 * d + ua2 * a * d ^ 2 + ua3 * d ^ 3) * N| + |(va0 * a ^ 3 + va1 * a ^ 2 * d + va2 * a * d ^ 2 + va3 * d ^ 3) * Dz| := abs_add_le _ _
      _ = |(ua0 * a ^ 3 + ua1 * a ^ 2 * d + ua2 * a * d ^ 2 + ua3 * d ^ 3)| * |N| + |(va0 * a ^ 3 + va1 * a ^ 2 * d + va2 * a * d ^ 2 + va3 * d ^ 3)| * |Dz| := by rw [abs_mul, abs_mul]
      _ ≤ ((|ua0| + |ua1| + |ua2| + |ua3|) * M ^ 3) * S +
            ((|va0| + |va1| + |va2| + |va3|) * M ^ 3) * S :=
          add_le_add (mul_le_mul hUa hNS (abs_nonneg _) (by positivity))
            (mul_le_mul hVa hDS (abs_nonneg _) (by positivity))
      _ ≤ _ := by
        have h := sum_bound (|ua0| + |ua1| + |ua2| + |ua3|) (|va0| + |va1| + |va2| + |va3|) (|ud0| + |ud1| + |ud2| + |ud3|) (|ve0| + |ve1| + |ve2| + |ve3|) (M ^ 3) S
          (by positivity) (by positivity) (by positivity) hP3 hS0
        exact h
  have hB : |Q * l ^ 8| * |d| ^ 7 ≤ (1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) +
      (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * M ^ 3 * S := by
    have h1 : |Q * l ^ 8 * d ^ 7| = |Q * l ^ 8| * |d| ^ 7 := by rw [abs_mul, abs_pow]
    rw [← h1, ← e2]
    calc |(ud0 * a ^ 3 + ud1 * a ^ 2 * d + ud2 * a * d ^ 2 + ud3 * d ^ 3) * N + (ve0 * a ^ 3 + ve1 * a ^ 2 * d + ve2 * a * d ^ 2 + ve3 * d ^ 3) * Dz| ≤ |(ud0 * a ^ 3 + ud1 * a ^ 2 * d + ud2 * a * d ^ 2 + ud3 * d ^ 3) * N| + |(ve0 * a ^ 3 + ve1 * a ^ 2 * d + ve2 * a * d ^ 2 + ve3 * d ^ 3) * Dz| := abs_add_le _ _
      _ = |(ud0 * a ^ 3 + ud1 * a ^ 2 * d + ud2 * a * d ^ 2 + ud3 * d ^ 3)| * |N| + |(ve0 * a ^ 3 + ve1 * a ^ 2 * d + ve2 * a * d ^ 2 + ve3 * d ^ 3)| * |Dz| := by rw [abs_mul, abs_mul]
      _ ≤ ((|ud0| + |ud1| + |ud2| + |ud3|) * M ^ 3) * S +
            ((|ve0| + |ve1| + |ve2| + |ve3|) * M ^ 3) * S :=
          add_le_add (mul_le_mul hUd hNS (abs_nonneg _) (by positivity))
            (mul_le_mul hVd hDS (abs_nonneg _) (by positivity))
      _ ≤ _ := by
        have h := sum_bound_d (|ua0| + |ua1| + |ua2| + |ua3|) (|va0| + |va1| + |va2| + |va3|) (|ud0| + |ud1| + |ud2| + |ud3|) (|ve0| + |ve1| + |ve2| + |ve3|) (M ^ 3) S
          (by positivity) (by positivity) (by positivity) hP3 hS0
        exact h
  have hM7 : |Q * l ^ 8| * M ^ 7 ≤ (1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) +
      (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * M ^ 3 * S := by
    rcases le_total d |a| with h | h
    · have hMa' : M = |a| := by rw [hMdef]; exact max_eq_left h
      calc |Q * l ^ 8| * M ^ 7 = |Q * l ^ 8| * |a| ^ 7 := by rw [hMa']
        _ ≤ _ := hA
    · have hMd' : M = d := by rw [hMdef]; exact max_eq_right h
      calc |Q * l ^ 8| * M ^ 7 = |Q * l ^ 8| * |d| ^ 7 := by rw [hMd', abs_of_pos hd]
        _ ≤ _ := hB
  constructor
  · have h7 : (|Q * l ^ 8| * M ^ 4) * M ^ 3 ≤ ((1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) + (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * S) * M ^ 3 := by
      calc (|Q * l ^ 8| * M ^ 4) * M ^ 3 = |Q * l ^ 8| * M ^ 7 := by ring
        _ ≤ (1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) + (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * M ^ 3 * S := hM7
        _ = ((1 + (|ua0| + |ua1| + |ua2| + |ua3| + (|va0| + |va1| + |va2| + |va3|)) + (|ud0| + |ud1| + |ud2| + |ud3| + (|ve0| + |ve1| + |ve2| + |ve3|))) * S) * M ^ 3 := by ring
    exact le_of_mul_le_mul_right h7 (by positivity)
  · have hqD : q ∣ Dz := by
      have hdv : q ∣ Dz * p := ⟨N, by rw [mul_comm]; exact hrel⟩
      exact hpq.symm.dvd_of_dvd_mul_right hdv
    obtain ⟨k, hk⟩ := hqD
    have hNk : N = p * k := by
      have h' : q * N = q * (p * k) := by rw [← hrel, hk]; ring
      exact mul_left_cancel₀ hq.ne' h'
    have hkN : k ∣ N := ⟨p, by rw [hNk]; ring⟩
    have hkD : k ∣ Dz := ⟨q, by rw [hk]; ring⟩
    have hkA : k ∣ Q * l ^ 8 * a ^ 7 := by
      rw [← e1]
      exact dvd_add (dvd_mul_of_dvd_right hkN _) (dvd_mul_of_dvd_right hkD _)
    have hkB : k ∣ Q * l ^ 8 * d ^ 7 := by
      rw [← e2]
      exact dvd_add (dvd_mul_of_dvd_right hkN _) (dvd_mul_of_dvd_right hkD _)
    have hac7 : IsCoprime (a ^ 7) (d ^ 7) := hac.pow
    obtain ⟨s, t, hst⟩ := hac7
    have hkQ : k ∣ Q * l ^ 8 := by
      have hsplit : Q * l ^ 8 = (Q * l ^ 8 * a ^ 7) * s + (Q * l ^ 8 * d ^ 7) * t := by
        linear_combination (-(Q * l ^ 8)) * hst
      rw [hsplit]
      exact dvd_add (dvd_mul_of_dvd_left hkA _) (dvd_mul_of_dvd_left hkB _)
    have hQl : Q * l ^ 8 ≠ 0 := mul_ne_zero hQ (pow_ne_zero 8 hl.ne')
    have hkle : |k| ≤ |Q * l ^ 8| :=
      Int.le_of_dvd (abs_pos.mpr hQl) ((abs_dvd_abs _ _).mpr hkQ)
    have hp1 : |p| ≤ max |p| q := le_max_left _ _
    have hq1 : q ≤ max |p| q := le_max_right _ _
    calc S ≤ (max |p| q) * |k| := by
          rw [hSdef]
          refine max_le ?_ ?_
          · rw [hNk, abs_mul]; exact mul_le_mul_of_nonneg_right hp1 (abs_nonneg k)
          · rw [hk, abs_mul, abs_of_pos hq]; exact mul_le_mul_of_nonneg_right hq1 (abs_nonneg k)
      _ ≤ (max |p| q) * |Q * l ^ 8| := mul_le_mul_of_nonneg_left hkle (le_trans (abs_nonneg p) hp1)
      _ = |Q * l ^ 8| * max |p| q := mul_comm _ _

-- Scaling: rational coefficients become integers after multiplying by L, L², L³, L⁴.
lemma scale_one (q : ℚ) (L : ℤ) (hL : (q.den : ℤ) ∣ L) (k : ℕ) (hk : 0 < k) :
    ∃ B : ℤ, (L : ℚ) ^ k * q = B := by
  obtain ⟨m, hm⟩ := hL
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨L ^ j * m * q.num, ?_⟩
  have hL' : (L : ℚ) = (q.den : ℚ) * m := by exact_mod_cast hm
  have hqn : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  push_cast
  rw [pow_succ, hL', ← hqn]
  ring

lemma scaling (b2 b4 b6 b8 : ℚ) :
    ∃ L : ℤ, 0 < L ∧ ∃ B2 B4 B6 B8 : ℤ, (L : ℚ) ^ 1 * b2 = B2 ∧ (L : ℚ) ^ 2 * b4 = B4 ∧
      (L : ℚ) ^ 3 * b6 = B6 ∧ (L : ℚ) ^ 4 * b8 = B8 := by
  refine ⟨(b2.den : ℤ) * b4.den * b6.den * b8.den, by positivity, ?_⟩
  obtain ⟨B2, hB2⟩ := scale_one b2 ((b2.den : ℤ) * b4.den * b6.den * b8.den)
    ⟨(b4.den : ℤ) * b6.den * b8.den, by push_cast; ring⟩ 1 (by norm_num)
  obtain ⟨B4, hB4⟩ := scale_one b4 ((b2.den : ℤ) * b4.den * b6.den * b8.den)
    ⟨(b2.den : ℤ) * b6.den * b8.den, by push_cast; ring⟩ 2 (by norm_num)
  obtain ⟨B6, hB6⟩ := scale_one b6 ((b2.den : ℤ) * b4.den * b6.den * b8.den)
    ⟨(b2.den : ℤ) * b4.den * b8.den, by push_cast; ring⟩ 3 (by norm_num)
  obtain ⟨B8, hB8⟩ := scale_one b8 ((b2.den : ℤ) * b4.den * b6.den * b8.den)
    ⟨(b2.den : ℤ) * b4.den * b6.den, by push_cast; ring⟩ 4 (by norm_num)
  exact ⟨B2, B4, B6, B8, hB2, hB4, hB6, hB8⟩

theorem main : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (H : E.toAffine.Point → ℝ),
    (∀ P : E.toAffine.Point, H P = match P with
      | WeierstrassCurve.Affine.Point.zero => 0
      | WeierstrassCurve.Affine.Point.some x _ _ =>
          Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ))) →
    ∃ D : ℝ, ∀ P : E.toAffine.Point, 4 * H P - D ≤ H (2 • P) := by
  intro E _ H hH
  obtain ⟨L, hL0, B2, B4, B6, B8, hB2, hB4, hB6, hB8⟩ := scaling E.b₂ E.b₄ E.b₆ E.b₈
  have hrelZ : 4 * B8 = B2 * B6 - B4 ^ 2 := by
    have h : ((4 * B8 : ℤ) : ℚ) = ((B2 * B6 - B4 ^ 2 : ℤ) : ℚ) := by
      push_cast
      rw [← hB2, ← hB4, ← hB6, ← hB8]
      linear_combination (L : ℚ) ^ 4 * E.b_relation
    exact_mod_cast h
  have hΔZ : -B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6 ≠ 0 := by
    intro h0
    have h1 : ((-B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6 : ℤ) : ℚ) = 0 := by
      exact_mod_cast h0
    have h2 : ((-B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6 : ℤ) : ℚ) =
        (L : ℚ) ^ 6 * E.Δ := by
      push_cast
      rw [← hB2, ← hB4, ← hB6, ← hB8]
      simp only [WeierstrassCurve.Δ]
      ring
    have hE : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
    have hL6 : (L : ℚ) ^ 6 ≠ 0 := pow_ne_zero 6 (by exact_mod_cast hL0.ne')
    have h3 : (L : ℚ) ^ 6 * E.Δ = 0 := by rw [← h2, h1]
    exact (mul_ne_zero hL6 hE) h3
  have hDQ : (B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) = (-B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6) ^ 2 := by
    linear_combination (-4 * (3 * B2 ^ 2 * B4 * B8 + B2 ^ 2 * B6 ^ 2 - 20 * B2 * B4 ^ 2 * B6
      - 8 * B2 * B6 * B8 + 16 * B4 ^ 4 - 28 * B4 ^ 2 * B8 + 81 * B4 * B6 ^ 2 + 16 * B8 ^ 2)) * hrelZ
  have hQ : (B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) ≠ 0 := by
    rw [hDQ]; exact pow_ne_zero 2 hΔZ
  obtain ⟨ua0, ua1, ua2, ua3, va0, va1, va2, va3, ud0, ud1, ud2, ud3, ve0, ve1, ve2, ve3, hU, hV⟩ :=
    coeff_ident L B2 B4 B6 B8
  obtain ⟨K, hK, hcore⟩ := core_bound L B2 B4 B6 B8 (B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) hL0 hQ
    ua0 ua1 ua2 ua3 va0 va1 va2 va3 ud0 ud1 ud2 ud3 ve0 ve1 ve2 ve3 hU hV
  -- The x-coordinates of 2-torsion points are roots of a nonzero cubic, hence finitely many.
  have hfin : {x : ℚ | 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0}.Finite := by
    have hp : (Polynomial.C (4 : ℚ) * Polynomial.X ^ 3 + Polynomial.C E.b₂ * Polynomial.X ^ 2 +
        Polynomial.C (2 * E.b₄) * Polynomial.X + Polynomial.C E.b₆ : Polynomial ℚ) ≠ 0 := by
      intro h0
      have h3 := congrArg (fun q : Polynomial ℚ => q.coeff 3) h0
      simp at h3
    refine (Polynomial.finite_setOf_isRoot hp).subset ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    linarith
  obtain ⟨Bt, hBt⟩ :=
    (hfin.image (fun x : ℚ => Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)))).bddAbove
  refine ⟨max (max (4 * Real.log 2 + Real.log (K : ℝ)) (4 * Bt)) 0, ?_⟩
  have hD1 : 4 * Real.log 2 + Real.log (K : ℝ) ≤
      max (max (4 * Real.log 2 + Real.log (K : ℝ)) (4 * Bt)) 0 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hD2 : 4 * Bt ≤ max (max (4 * Real.log 2 + Real.log (K : ℝ)) (4 * Bt)) 0 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hD3 : (0 : ℝ) ≤ max (max (4 * Real.log 2 + Real.log (K : ℝ)) (4 * Bt)) 0 := le_max_right _ _
  intro P
  have hH0 : H WeierstrassCurve.Affine.Point.zero = 0 := by rw [hH]
  cases P with
  | zero =>
    have h2z : (2 : ℕ) • (WeierstrassCurve.Affine.Point.zero : E.toAffine.Point) =
        WeierstrassCurve.Affine.Point.zero := nsmul_zero _
    rw [h2z, hH0]
    linarith
  | some x y h =>
    by_cases hy : y = E.toAffine.negY x y
    · have hP2 : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h : E.toAffine.Point) =
          WeierstrassCurve.Affine.Point.zero := by
        rw [two_nsmul]; exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
      have hcub : 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 := by
        have hc := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
        have hy' : y = -y - E.a₁ * x - E.a₃ := hy
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
        linear_combination (2 * y + E.a₁ * x + E.a₃) * hy' - 4 * hc
      have hHP : H (WeierstrassCurve.Affine.Point.some x y h) =
          Real.log (1 + max (x.num.natAbs : ℝ) (x.den : ℝ)) := by
        rw [hH]
      have hbd := hBt (Set.mem_image_of_mem _ (show x ∈ {x : ℚ | 4 * x ^ 3 + E.b₂ * x ^ 2 +
        2 * E.b₄ * x + E.b₆ = 0} from hcub))
      rw [hP2, hH0, hHP]
      linarith
    · obtain ⟨x', y', h', hP2, hx'⟩ := MPP.Solutions.Bsd037.main E x y h hy
      rw [two_nsmul, hP2]
      set a : ℤ := x.num with ha
      set d : ℤ := (x.den : ℤ) with hd
      set p : ℤ := x'.num with hp
      set q : ℤ := (x'.den : ℤ) with hq
      have hd0 : 0 < d := by rw [hd]; exact_mod_cast x.den_pos
      have hq0 : 0 < q := by rw [hq]; exact_mod_cast x'.den_pos
      have hcop : IsCoprime a d := Int.isCoprime_iff_gcd_eq_one.mpr x.reduced
      have hpq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr x'.reduced
      have hX : (a : ℚ) = x * (d : ℚ) := by
        rw [ha, hd]; push_cast; exact (Rat.mul_den_eq_num x).symm
      have hX' : (p : ℚ) = x' * (q : ℚ) := by
        rw [hp, hq]; push_cast; exact (Rat.mul_den_eq_num x').symm
      have hZ : p * (d * (4 * L ^ 4 * a ^ 3 + B2 * L ^ 3 * a ^ 2 * d + 2 * B4 * L ^ 2 * a * d ^ 2 +
          B6 * L * d ^ 3)) = q * (L ^ 4 * a ^ 4 - B4 * L ^ 2 * a ^ 2 * d ^ 2 - 2 * B6 * L * a * d ^ 3 -
          B8 * d ^ 4) := by
        apply @Int.cast_injective ℚ _ _
        push_cast
        rw [hX', hX, ← hB2, ← hB4, ← hB6, ← hB8]
        linear_combination (q : ℚ) * (L : ℚ) ^ 4 * (d : ℚ) ^ 4 * hx'
      obtain ⟨hi, hii⟩ := hcore a d p q hd0 hcop hq0 hpq hZ
      have hT : (0 : ℤ) < |(B2^4*B8^2 - 6*B2^3*B4*B6*B8 + 4*B2^3*B6^3 + 4*B2^2*B4^3*B8 - 3*B2^2*B4^2*B6^2 - 48*B2^2*B4*B8^2 + 6*B2^2*B6^2*B8 + 240*B2*B4^2*B6*B8 - 162*B2*B4*B6^3 + 192*B2*B6*B8^2 - 144*B4^4*B8 + 108*B4^3*B6^2 + 384*B4^2*B8^2 - 1296*B4*B6^2*B8 + 729*B6^4 - 256*B8^3) * L ^ 8| := abs_pos.mpr (mul_ne_zero hQ (pow_ne_zero 8 hL0.ne'))
      have hM4 : (max |a| d) ^ 4 ≤ K * max |p| q := by
        refine le_of_mul_le_mul_left ?_ hT
        exact hi.trans (le_trans (mul_le_mul_of_nonneg_left hii hK.le) (le_of_eq (by ring)))
      have hM1 : (1 : ℤ) ≤ max |a| d := le_trans (by omega) (le_max_right _ _)
      have hHP : H (WeierstrassCurve.Affine.Point.some x y h) =
          Real.log (1 + ((max |a| d : ℤ) : ℝ)) := by
        rw [hH]
        show Real.log (1 + max ((x.num.natAbs : ℕ) : ℝ) ((x.den : ℕ) : ℝ)) = _
        congr 2
        rw [Int.cast_max, Int.cast_abs, Nat.cast_natAbs, Int.cast_natCast, Int.cast_abs]
      have hHP2 : H (WeierstrassCurve.Affine.Point.some x' y' h') =
          Real.log (1 + ((max |p| q : ℤ) : ℝ)) := by
        rw [hH]
        show Real.log (1 + max ((x'.num.natAbs : ℕ) : ℝ) ((x'.den : ℕ) : ℝ)) = _
        congr 2
        rw [Int.cast_max, Int.cast_abs, Nat.cast_natAbs, Int.cast_natCast, Int.cast_abs]
      rw [hHP, hHP2]
      have hKr : (0 : ℝ) < K := by exact_mod_cast hK
      have hMr : (1 : ℝ) ≤ ((max |a| d : ℤ) : ℝ) := by exact_mod_cast hM1
      have hMr0 : (0 : ℝ) < ((max |a| d : ℤ) : ℝ) := by linarith
      have hK4 : ((max |a| d : ℤ) : ℝ) ^ 4 ≤ (K : ℝ) * ((max |p| q : ℤ) : ℝ) := by
        exact_mod_cast hM4
      have hA1 : Real.log (1 + ((max |a| d : ℤ) : ℝ)) ≤
          Real.log 2 + Real.log ((max |a| d : ℤ) : ℝ) := by
        rw [← Real.log_mul (by norm_num) hMr0.ne']
        exact Real.log_le_log (by linarith) (by linarith)
      have hB1 : 4 * Real.log ((max |a| d : ℤ) : ℝ) - Real.log (K : ℝ) ≤
          Real.log (1 + ((max |p| q : ℤ) : ℝ)) := by
        have hpos : 0 < ((max |a| d : ℤ) : ℝ) ^ 4 / (K : ℝ) := div_pos (pow_pos hMr0 4) hKr
        have h2 : Real.log (((max |a| d : ℤ) : ℝ) ^ 4 / (K : ℝ)) =
            4 * Real.log ((max |a| d : ℤ) : ℝ) - Real.log (K : ℝ) := by
          rw [Real.log_div (pow_pos hMr0 4).ne' hKr.ne', Real.log_pow]
          push_cast
          ring
        rw [← h2]
        apply Real.log_le_log hpos
        rw [div_le_iff₀ hKr]
        nlinarith
      linarith [hA1, hB1, hD1]

end MPP.Solutions.Bsd043
