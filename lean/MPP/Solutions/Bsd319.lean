import Mathlib
import MPP.Solutions.Bsd255
import MPP.Solutions.Bsd317
import MPP.Solutions.Bsd318

namespace MPP.Solutions.Bsd319

open Polynomial

-- the coefficient of Σ_i X^(p i) r i at p j + t, for t < K ≤ p, is the coefficient of r j at t
lemma coeff_sum_shift (p K J : ℕ) (hKp : K ≤ p) (r : Fin J → Polynomial (ZMod p))
    (hr : ∀ j, (r j).natDegree < K) (j : Fin J) (t : ℕ) (ht : t < K) :
    (∑ i : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (i : ℕ)) * r i).coeff (p * (j : ℕ) + t)
      = (r j).coeff t := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left]
  · intro i _ hij
    rw [Polynomial.coeff_X_pow_mul']
    split_ifs with h
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hlt : (i : ℕ) < (j : ℕ) := by
        rcases Nat.lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with h1 | h1
        · exact h1
        · exfalso
          have h2 : p * ((j : ℕ) + 1) ≤ p * (i : ℕ) := Nat.mul_le_mul_left p h1
          rw [Nat.mul_add, Nat.mul_one] at h2
          omega
      have e : p * (j : ℕ) = p * (i : ℕ) + p * ((j : ℕ) - (i : ℕ)) := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hlt.le]
      have h3 : p * 1 ≤ p * ((j : ℕ) - (i : ℕ)) := Nat.mul_le_mul_left p (by omega)
      rw [Nat.mul_one] at h3
      have := hr i
      omega
    · rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), 2 < p → 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    (Matrix.of (fun (i t : Fin ((p - 1) / 2)) =>
      Polynomial.C (((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2)).coeff
          ((p - 1) / 2 + (i : ℕ) - (t : ℕ))) +
        Polynomial.C (((Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2)).coeff
          ((p - 1) / 2 + (i : ℕ) - (t : ℕ) + p)) * (Polynomial.X : Polynomial (ZMod p)))).det ≠ 0 →
    ∀ (J : ℕ) (r₀ r₁ : Fin J → Polynomial (ZMod p)),
      (∀ j, (r₀ j).natDegree < (p - 1) / 2) → (∀ j, (r₁ j).natDegree < (p - 1) / 2) →
      ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) *
        (r₀ j + r₁ j * (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2)) = 0 →
      ∀ j, r₀ j = 0 ∧ r₁ j = 0 := by
  intro p _ a b hp _ hdet J r₀ r₁ hr₀ hr₁ hsum
  set K := (p - 1) / 2 with hKdef
  set g := (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ K with hg
  have hK1 : 1 ≤ K := by omega
  have hKp : K ≤ p := by omega
  have hdeg3 : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b :
      Polynomial (ZMod p)).natDegree ≤ 3 := by
    compute_degree!
  have hgdeg : g.natDegree < 2 * p := by
    calc g.natDegree ≤ K * (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b :
          Polynomial (ZMod p)).natDegree := Polynomial.natDegree_pow_le
      _ ≤ K * 3 := Nat.mul_le_mul_left K hdeg3
      _ < 2 * p := by omega
  -- A + g B = 0, with A and B the two sums over Fin J
  have hsplit : ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₀ j
      + g * ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₁ j = 0 := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- extend r₁ by zero to a function on ℕ
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → Polynomial (ZMod p),
      R = fun j => if h : j < J then r₁ ⟨j, h⟩ else 0 := ⟨_, rfl⟩
  have hRval : ∀ j : Fin J, R j = r₁ j := by
    intro j
    rw [hRdef]
    simp
  have hRJ : ∀ j, J ≤ j → R j = 0 := by
    intro j hj
    rw [hRdef]
    simp only
    rw [dif_neg (by omega)]
  have hRdeg : ∀ j, (R j).natDegree < K := by
    intro j
    rw [hRdef]
    by_cases h : j < J
    · simp only [dif_pos h]
      exact hr₁ _
    · simp only [dif_neg h, Polynomial.natDegree_zero]
      omega
  have hB : ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₁ j
      = ∑ j ∈ Finset.range J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * j) * R j := by
    have := Fin.sum_univ_eq_sum_range
      (fun j => (Polynomial.X : Polynomial (ZMod p)) ^ (p * j) * R j) J
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => by rw [hRval j])
  -- the coefficients of g B at p q + (K + i) are minus those of A, which vanish there
  have hcoef : ∀ u, (g * ∑ j ∈ Finset.range J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * j) * R j).coeff u
      = -(∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₀ j).coeff u := by
    intro u
    rw [← hB]
    have := congrArg (fun F => F.coeff u) hsplit
    simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at this
    linear_combination this
  -- bsd-318 gives R = 0 from the Toeplitz determinant
  have hsys : ∀ q : ℕ, ∀ i : Fin K,
      ∑ t ∈ Finset.range K, (g.coeff (K + (i : ℕ) - t) * (R q).coeff t +
        (if 0 < q then g.coeff (K + (i : ℕ) - t + p) * (R (q - 1)).coeff t else 0)) = 0 := by
    intro q i
    have h317 := MPP.Solutions.Bsd317.main p K J g R hgdeg hRJ hRdeg (K + (i : ℕ)) q
      (by omega) (by have := i.isLt; omega)
    have hmod : (p * q + (K + (i : ℕ))) % p = K + (i : ℕ) := by
      have := i.isLt
      simp [Nat.add_mod, Nat.mod_eq_of_lt (show K + (i : ℕ) < p by omega)]
    have hA0 := MPP.Solutions.Bsd255.main p K J r₀ hr₀ (p * q + (K + (i : ℕ)))
      (by rw [hmod]; omega)
    rw [hcoef, hA0, neg_zero] at h317
    exact h317.symm
  have hR0 : ∀ j, R j = 0 :=
    MPP.Solutions.Bsd318.main p K J g R hRJ hRdeg hdet hsys
  -- hence B = 0, so A = 0
  have hB' : ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₁ j = 0 := by
    rw [hB]
    exact Finset.sum_eq_zero (fun j _ => by rw [hR0 j, mul_zero])
  have hA0 : ∑ j : Fin J, (Polynomial.X : Polynomial (ZMod p)) ^ (p * (j : ℕ)) * r₀ j = 0 := by
    rw [hB', mul_zero, add_zero] at hsplit
    exact hsplit
  -- the coefficients of A at p j + t recover those of r₀ j, so r₀ j = 0
  have hr₀0 : ∀ j : Fin J, r₀ j = 0 := by
    intro j
    apply Polynomial.ext
    intro n
    by_cases hn : n < K
    · have h0 := coeff_sum_shift p K J hKp r₀ hr₀ j n hn
      rw [hA0, Polynomial.coeff_zero] at h0
      rw [Polynomial.coeff_zero]
      exact h0.symm
    · rw [Polynomial.coeff_zero]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hr₀ j) (by omega))
  intro j
  refine ⟨hr₀0 j, ?_⟩
  rw [← hRval j]
  exact hR0 j

end MPP.Solutions.Bsd319
