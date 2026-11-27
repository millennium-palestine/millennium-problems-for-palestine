import Mathlib

namespace MPP.Solutions.Bsd366

open Polynomial

theorem main : ∀ (K : Type) [Field K] (a b : K),
    (36 : K) ^ 11 *
      (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
            - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
        (X ^ 3 + C a * X + C b) ^ 2
      - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3).resultant
        (derivative (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
            - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
        (X ^ 3 + C a * X + C b) ^ 2
      - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3)) 12 11 =
    12 ^ 11 * 3600 *
      (31 * C a * X ^ 10 + 285 * C b * X ^ 9 - 105 * C (a ^ 2) * X ^ 8 + 300 * C (a * b) * X ^ 7
      - 450 * C (a ^ 3) * X ^ 6 - 360 * C (b ^ 2) * X ^ 6 - 1218 * C (a ^ 2 * b) * X ^ 5
      - 250 * C (a ^ 4) * X ^ 4 - 3840 * C (a * b ^ 2) * X ^ 4 - 180 * C (a ^ 3 * b) * X ^ 3
      - 3600 * C (b ^ 3) * X ^ 3 - 125 * C (a ^ 5) * X ^ 2 - 600 * C (a ^ 2 * b ^ 2) * X ^ 2
      - 275 * C (a ^ 4 * b) * X - 1760 * C (a * b ^ 3) * X + 3 * C (a ^ 6) - 96 * C (a ^ 3 * b ^ 2)
      - 768 * C (b ^ 4)).resultant
        (derivative (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
            - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
        (X ^ 3 + C a * X + C b) ^ 2
      - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3)) 10 11 := by
  intro K _ a b
  -- the resultant transfer, for any f with 36 f = 3 X f′ + 12 N, leading coefficient 5 at degree 12
  have key : ∀ (f N : K[X]),
      36 * f = 3 * X * derivative f + 12 * N → f.natDegree ≤ 12 → f.coeff 12 = 5 →
      N.natDegree ≤ 10 →
      (36 : K) ^ 11 * f.resultant (derivative f) 12 11 =
        12 ^ 11 * 3600 * N.resultant (derivative f) 10 11 := by
    intro f N hE hfd hf12 hN
    have hg : (derivative f).natDegree ≤ 11 := (natDegree_derivative_le f).trans (by omega)
    have hp : (3 * X : K[X]).natDegree ≤ 1 := by compute_degree!
    have hc11 : (derivative f).coeff 11 = 60 := by
      rw [coeff_derivative, hf12]; norm_num
    have c36 : (C (36 : K)) = 36 := map_ofNat C 36
    have c12 : (C (12 : K)) = 12 := map_ofNat C 12
    have hE' : C (36 : K) * f = C 12 * N + derivative f * (3 * X) := by
      rw [c36, c12]; linear_combination hE
    have hR := resultant_add_left_deg (f := N) (g := derivative f) (m := 10) (k := 2) (n := 11) hN
    rw [show 10 + 2 = 12 from rfl] at hR
    rw [← resultant_C_mul_left (f := f) (g := derivative f) (m := 12) (n := 11) 36, hE',
      resultant_add_mul_left (p := 3 * X) (hk := by omega) (hg := hg), resultant_C_mul_left, hR, hc11]
    ring
  refine key _ _ ?_ ?_ ?_ ?_
  · simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_C,
      derivative_X, derivative_neg, map_pow, map_mul, map_sub, map_add, map_neg, map_zero,
      map_ofNat C, map_one, map_natCast C, Nat.cast_ofNat]
    norm_num [map_ofNat C]
    ring
  · compute_degree!
  · compute_degree!
  · compute_degree!

end MPP.Solutions.Bsd366
