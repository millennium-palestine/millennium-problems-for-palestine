import Mathlib

namespace MPP.Solutions.Bsd194

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), 2 < p →
    (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)) *
      ((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2)) ^ 2 =
    Polynomial.X ^ (3 * p) + Polynomial.C a * Polynomial.X ^ p + Polynomial.C b := by
  intro p _ a b hp
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hc : (p - 1) / 2 = k := by omega
  have hpk : p = (p - 1) / 2 * 2 + 1 := by omega
  have hfp : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)) ^ p =
      Polynomial.X ^ (3 * p) + Polynomial.C a * Polynomial.X ^ p + Polynomial.C b := by
    rw [← ZMod.expand_card]
    simp only [map_add, map_mul, map_pow, expand_X, expand_C]
    ring
  calc _ = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial (ZMod p)) ^ p := by
        rw [← pow_mul, ← pow_succ', ← hpk]
    _ = _ := hfp

end MPP.Solutions.Bsd194
