import Mathlib

namespace MPP.Solutions.Bsd380

open Polynomial

set_option maxHeartbeats 4000000

theorem main : ∀ (K : Type) [Field K] (a b : K) (N g R : K[X]),
  N = 31 * C a * X ^ 10 + 285 * C b * X ^ 9 - 105 * C (a ^ 2) * X ^ 8 + 300 * C (a * b) * X ^ 7
    - 450 * C (a ^ 3) * X ^ 6 - 360 * C (b ^ 2) * X ^ 6 - 1218 * C (a ^ 2 * b) * X ^ 5
    - 250 * C (a ^ 4) * X ^ 4 - 3840 * C (a * b ^ 2) * X ^ 4 - 180 * C (a ^ 3 * b) * X ^ 3
    - 3600 * C (b ^ 3) * X ^ 3 - 125 * C (a ^ 5) * X ^ 2 - 600 * C (a ^ 2 * b ^ 2) * X ^ 2
    - 275 * C (a ^ 4 * b) * X - 1760 * C (a * b ^ 3) * X + 3 * C (a ^ 6) - 96 * C (a ^ 3 * b ^ 2)
    - 768 * C (b ^ 4) →
  g = derivative (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
          - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
      (X ^ 3 + C a * X + C b) ^ 2
    - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3) →
  R = (- 44800 * C (a ^ 6 * b) - 2256640 * C (a ^ 3 * b ^ 3) - 13132800 * C (b ^ 5)
    + (- 101680 * C (a ^ 7) - 4985220 * C (a ^ 4 * b ^ 2) - 28667520 * C (a * b ^ 4)) * X
    + (- 1856640 * C (a ^ 5 * b) - 11599200 * C (a ^ 2 * b ^ 3)) * X ^ 2
    + (- 248000 * C (a ^ 6) - 9342480 * C (a ^ 3 * b ^ 2) - 61560000 * C (b ^ 4)) * X ^ 3
    + (- 7284480 * C (a ^ 4 * b) - 58968000 * C (a * b ^ 3)) * X ^ 4
    + (- 1264800 * C (a ^ 5) - 15069240 * C (a ^ 2 * b ^ 2)) * X ^ 5
    + (- 3815040 * C (a ^ 3 * b) - 6156000 * C (b ^ 3)) * X ^ 6
    + (29760 * C (a ^ 4) + 5799600 * C (a * b ^ 2)) * X ^ 7
    + 933120 * C (a ^ 2 * b) * X ^ 8
    + (791120 * C (a ^ 3) + 4873500 * C (b ^ 2)) * X ^ 9) →
  (31 * a) ^ 20 * N.resultant g 10 11 = N.resultant R 10 11 := by
  intro K _ a b N g R hN hg hR
  have hC : C ((31 * a) ^ 2) = (31 * C a) ^ 2 := by
    simp only [map_pow, map_mul, map_ofNat]
  have key : C ((31 * a) ^ 2) * g = R + N * (60 * (31 * C a * X - 285 * C b)) := by
    rw [hC, hg, hN, hR]
    simp only [derivative_mul, derivative_pow, derivative_C, derivative_X, derivative_ofNat,
      map_mul, map_pow, map_add, map_sub, map_ofNat, Nat.cast_ofNat]
    ring
  have hdeg : N.natDegree ≤ 10 := by
    rw [hN]
    compute_degree!
  have hq1 : (60 * (31 * C a * X - 285 * C b)).natDegree ≤ 1 := by
    compute_degree!
  have hq : (60 * (31 * C a * X - 285 * C b)).natDegree + 10 ≤ 11 := by omega
  have h1 := resultant_add_mul_right (f := N) (g := R) (p := 60 * (31 * C a * X - 285 * C b))
    (m := 10) (n := 11) hq hdeg
  have h2 := resultant_C_mul_right (f := N) (g := g) (r := (31 * a) ^ 2) (m := 10) (n := 11)
  rw [← h1, ← key, h2]
  ring

end MPP.Solutions.Bsd380
