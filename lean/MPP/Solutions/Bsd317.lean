import Mathlib

namespace MPP.Solutions.Bsd317

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K J : ℕ) (g : Polynomial (ZMod p)) (r : ℕ → Polynomial (ZMod p)),
    g.natDegree < 2 * p →
    (∀ j, J ≤ j → r j = 0) →
    (∀ j, (r j).natDegree < K) →
    ∀ ρ q : ℕ, K ≤ ρ → ρ < p →
      (g * ∑ j ∈ Finset.range J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * j) * r j).coeff (p * q + ρ) =
        ∑ t ∈ Finset.range K, (g.coeff (ρ - t) * (r q).coeff t +
          (if 0 < q then g.coeff (ρ - t + p) * (r (q - 1)).coeff t else 0)) := by
  intro p _ K J g r hg hrJ hrK ρ q hKρ hρp
  -- coefficient of g * (X^(p*j) * r j) through the coefficients of r j
  have hcoef : ∀ j N : ℕ, (g * ((Polynomial.X : Polynomial (ZMod p)) ^ (p * j) * r j)).coeff N =
      ∑ t ∈ Finset.range K, if p * j + t ≤ N then g.coeff (N - (p * j + t)) * (r j).coeff t else 0 := by
    intro j N
    have hr : r j = ∑ t ∈ Finset.range K, C ((r j).coeff t) * X ^ t := by
      conv_lhs => rw [as_sum_range' (r j) K (hrK j)]
      simp only [C_mul_X_pow_eq_monomial]
    have hsplit : g * (X ^ (p * j) * r j) =
        ∑ t ∈ Finset.range K, (g * X ^ (p * j + t)) * C ((r j).coeff t) := by
      conv_lhs => rw [hr]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [pow_add]
      ring
    rw [hsplit, finsetSum_coeff]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [coeff_mul_C, coeff_mul_X_pow']
    by_cases h : p * j + t ≤ N <;> simp [h]
  rw [Finset.mul_sum, finsetSum_coeff]
  simp only [hcoef]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htK : t < K := Finset.mem_range.mp ht
  have hpoint : ∀ j ∈ Finset.range J,
      (if p * j + t ≤ p * q + ρ then g.coeff (p * q + ρ - (p * j + t)) * (r j).coeff t else 0) =
        (if j = q then g.coeff (ρ - t) * (r j).coeff t else 0) +
        (if j + 1 = q then g.coeff (ρ - t + p) * (r j).coeff t else 0) := by
    intro j _
    rcases lt_trichotomy j q with hjq | rfl | hjq
    · by_cases h1 : j + 1 = q
      · obtain rfl : q = j + 1 := h1.symm
        have e : p * (j + 1) + ρ - (p * j + t) = ρ - t + p := by
          rw [Nat.mul_succ]
          omega
        rw [if_pos (by rw [Nat.mul_succ]; omega), e, if_neg (by omega), if_pos rfl, zero_add]
      · have hj2 : 2 * p ≤ p * q + ρ - (p * j + t) := by
          have : p * (j + 2) ≤ p * q := Nat.mul_le_mul_left p (by omega)
          rw [Nat.mul_add] at this
          omega
        rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hg hj2)]
        simp [h1, show j ≠ q by omega]
    · simp [Nat.add_sub_add_left, show t ≤ ρ by omega]
    · have hpj : p * (q + 1) ≤ p * j := Nat.mul_le_mul_left p hjq
      rw [Nat.mul_succ] at hpj
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
  have h1 : ∑ j ∈ Finset.range J, (if j = q then g.coeff (ρ - t) * (r j).coeff t else 0) =
      g.coeff (ρ - t) * (r q).coeff t := by
    by_cases hq : q ∈ Finset.range J
    · rw [Finset.sum_ite_eq' (Finset.range J) q (fun j => g.coeff (ρ - t) * (r j).coeff t)]
      simp [hq]
    · have hr0 : r q = 0 := hrJ q (by simp at hq; omega)
      rw [hr0]
      simp only [Polynomial.coeff_zero, mul_zero]
      refine Finset.sum_eq_zero fun j hj => if_neg fun h : j = q => hq (h ▸ hj)
  have h2 : ∑ j ∈ Finset.range J, (if j + 1 = q then g.coeff (ρ - t + p) * (r j).coeff t else 0) =
      if 0 < q then g.coeff (ρ - t + p) * (r (q - 1)).coeff t else 0 := by
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · subst hq0
      simp
    · rw [if_pos hqpos]
      have hc : ∀ j, (j + 1 = q) ↔ (j = q - 1) := fun j => by omega
      simp only [hc]
      by_cases hq : q - 1 ∈ Finset.range J
      · rw [Finset.sum_ite_eq' (Finset.range J) (q - 1) (fun j => g.coeff (ρ - t + p) * (r j).coeff t)]
        simp [hq]
      · have hr0 : r (q - 1) = 0 := hrJ _ (by simp at hq; omega)
        rw [hr0]
        simp only [Polynomial.coeff_zero, mul_zero]
        refine Finset.sum_eq_zero fun j hj => if_neg fun h : j = q - 1 => hq (h ▸ hj)
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, h1, h2]

end MPP.Solutions.Bsd317
