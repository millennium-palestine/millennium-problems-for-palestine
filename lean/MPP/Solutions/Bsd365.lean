import Mathlib

namespace MPP.Solutions.Bsd365

open Polynomial

theorem main : ∀ (K : Type) [Field K] (a b : K),
    36 * (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
            - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
        (X ^ 3 + C a * X + C b) ^ 2
      - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3) =
    3 * X * derivative (32 * (X ^ 6 + 5 * C a * X ^ 4 + 20 * C b * X ^ 3 - 5 * C (a ^ 2) * X ^ 2
            - 4 * C (a * b) * X - C (a ^ 3) - 8 * C (b ^ 2)) *
        (X ^ 3 + C a * X + C b) ^ 2
      - (3 * X ^ 4 + 6 * C a * X ^ 2 + 12 * C b * X - C (a ^ 2)) ^ 3) +
    12 * (31 * C a * X ^ 10 + 285 * C b * X ^ 9 - 105 * C (a ^ 2) * X ^ 8 + 300 * C (a * b) * X ^ 7
      - 450 * C (a ^ 3) * X ^ 6 - 360 * C (b ^ 2) * X ^ 6 - 1218 * C (a ^ 2 * b) * X ^ 5
      - 250 * C (a ^ 4) * X ^ 4 - 3840 * C (a * b ^ 2) * X ^ 4 - 180 * C (a ^ 3 * b) * X ^ 3
      - 3600 * C (b ^ 3) * X ^ 3 - 125 * C (a ^ 5) * X ^ 2 - 600 * C (a ^ 2 * b ^ 2) * X ^ 2
      - 275 * C (a ^ 4 * b) * X - 1760 * C (a * b ^ 3) * X + 3 * C (a ^ 6) - 96 * C (a ^ 3 * b ^ 2)
      - 768 * C (b ^ 4)) := by
  intro K _ a b
  simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_C,
    derivative_X, derivative_neg, map_pow, map_mul, map_sub, map_add, map_neg, map_zero,
    map_ofNat C, map_one, map_natCast C, Nat.cast_ofNat]
  norm_num [map_ofNat C]
  ring

end MPP.Solutions.Bsd365
