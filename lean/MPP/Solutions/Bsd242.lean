import Mathlib

namespace MPP.Solutions.Bsd242

open Polynomial

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (b2 b4 b6 : K), (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    b2 ^ 3 * b6 - b2 ^ 2 * b4 ^ 2 - 36 * b2 * b4 * b6 + 32 * b4 ^ 3 + 108 * b6 ^ 2 ≠ 0 →
    ∃ f : Fin 4 → K, Function.Injective f ∧
      ∀ i, 12 * f i ^ 4 + 4 * b2 * f i ^ 3 + 12 * b4 * f i ^ 2 + 12 * b6 * f i + (b2 * b6 - b4 ^ 2) = 0 := by
  intro K _ _ b2 b4 b6 h2 h3 hQ
  classical
  set Q : K := b2 ^ 3 * b6 - b2 ^ 2 * b4 ^ 2 - 36 * b2 * b4 * b6 + 32 * b4 ^ 3 + 108 * b6 ^ 2 with hQdef
  set P : K[X] := 12 * X ^ 4 + 4 * C b2 * X ^ 3 + 12 * C b4 * X ^ 2 + 12 * C b6 * X
    + C (b2 * b6 - b4 ^ 2) with hPdef
  have hC0 : (C (b2 * b6 - b4 ^ 2) : K[X]) = C b2 * C b6 - C b4 ^ 2 := by
    rw [C_sub, C_mul, C_pow]
  set D : K[X] := 48 * X ^ 3 + 12 * C b2 * X ^ 2 + 24 * C b4 * X + 12 * C b6 with hDdef
  set a1 : K[X] := -(C b2) ^ 2 + 8 * C b2 * X + 32 * C b4 + 48 * X ^ 2 with ha1def
  set b1 : K[X] := -(C b2) ^ 2 * X - C b2 * C b4 + 9 * C b2 * X ^ 2 + 42 * C b4 * X + 27 * C b6
    + 36 * X ^ 3 with hb1def
  have h12 : (12 : K) ≠ 0 := by
    have e : (12 : K) = 2 * 2 * 3 := by norm_num
    rw [e]
    exact mul_ne_zero (mul_ne_zero h2 h2) h3
  -- P has degree 4 with leading coefficient 12
  have hdeg : P.natDegree = 4 := by
    rw [hPdef]
    compute_degree!
  -- the derivative of P
  have hD : derivative P = D := by
    rw [hPdef, derivative_add, derivative_C, add_zero, hDdef]
    simp [map_ofNat]
    ring
  -- the Bezout certificate: 3Q = b1 * P' - 3 a1 * P
  have hQC : C Q = C b2 ^ 3 * C b6 - C b2 ^ 2 * C b4 ^ 2 - 36 * C b2 * C b4 * C b6
      + 32 * C b4 ^ 3 + 108 * C b6 ^ 2 := by
    rw [hQdef]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  have hcert : 3 * C Q = b1 * D - 3 * a1 * P := by
    rw [hQC, hDdef, hPdef, hC0, ha1def, hb1def]
    ring
  have hQ3 : (3 : K) * Q ≠ 0 := mul_ne_zero h3 hQ
  -- P is separable, so its roots are distinct
  have hsep : P.Separable := by
    unfold Separable
    rw [hD]
    have hc : (C ((3 * Q)⁻¹) : K[X]) * (3 * C Q) = 1 := by
      rw [show (3 : K[X]) * C Q = C (3 * Q) by simp only [map_mul, map_ofNat]]
      rw [← C_mul, inv_mul_cancel₀ hQ3, C_1]
    refine ⟨-(C ((3 * Q)⁻¹) * (3 * a1)), C ((3 * Q)⁻¹) * b1, ?_⟩
    linear_combination hc - C ((3 * Q)⁻¹) * hcert
  have hnodup : P.roots.Nodup := nodup_roots hsep
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hcard : Multiset.card P.roots = 4 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hScard : Fintype.card P.roots.toFinset = 4 := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hrootEq : ∀ a ∈ P.roots,
      12 * a ^ 4 + 4 * b2 * a ^ 3 + 12 * b4 * a ^ 2 + 12 * b6 * a + (b2 * b6 - b4 ^ 2) = 0 := by
    intro a ha
    have h0 : eval a P = 0 := (mem_roots hP0).mp ha
    rw [hPdef] at h0
    simp at h0
    linear_combination h0
  let e := Fintype.equivFinOfCardEq hScard
  refine ⟨fun i => ((e.symm i : P.roots.toFinset) : K), ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact hrootEq _ (Multiset.mem_toFinset.mp (e.symm i).2)

end MPP.Solutions.Bsd242
