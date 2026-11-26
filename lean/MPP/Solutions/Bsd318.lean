import Mathlib

namespace MPP.Solutions.Bsd318

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K N : ℕ) (g : Polynomial (ZMod p)) (r : ℕ → Polynomial (ZMod p)),
    (∀ j, N ≤ j → r j = 0) →
    (∀ j, (r j).natDegree < K) →
    (Matrix.of (fun (i t : Fin K) =>
      Polynomial.C (g.coeff (K + (i : ℕ) - (t : ℕ))) +
        Polynomial.C (g.coeff (K + (i : ℕ) - (t : ℕ) + p)) * (Polynomial.X : Polynomial (ZMod p)))).det ≠ 0 →
    (∀ q : ℕ, ∀ i : Fin K,
      ∑ t ∈ Finset.range K, (g.coeff (K + (i : ℕ) - t) * (r q).coeff t +
        (if 0 < q then g.coeff (K + (i : ℕ) - t + p) * (r (q - 1)).coeff t else 0)) = 0) →
    ∀ j, r j = 0 := by
  intro p _ K N g r hrN hrK hdet hsys j
  -- expansion of the product of the Toeplitz row with the generating function
  have expand : ∀ (c d : ℕ → ZMod p) (A : ℕ → ℕ → ZMod p) (M : ℕ),
      ∑ t ∈ Finset.range K, (C (c t) + C (d t) * X) * ∑ q ∈ Finset.range M, C (A q t) * X ^ q =
        ∑ q ∈ Finset.range M, X ^ q * C (∑ t ∈ Finset.range K, c t * A q t) +
          ∑ q ∈ Finset.range M, X ^ (q + 1) * C (∑ t ∈ Finset.range K, d t * A q t) := by
    intro c d A M
    have last : ∀ M : ℕ, ∑ t ∈ Finset.range K, (C (c t) + C (d t) * X) * (C (A M t) * X ^ M) =
        X ^ M * C (∑ t ∈ Finset.range K, c t * A M t) +
          X ^ (M + 1) * C (∑ t ∈ Finset.range K, d t * A M t) := by
      intro M
      rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, map_mul]
      ring
    induction M with
    | zero => simp
    | succ M ih =>
      simp only [Finset.sum_range_succ, mul_add, Finset.sum_add_distrib]
      rw [ih, last M]
      ring
  -- the Toeplitz row identity for each i < K
  have core : ∀ i : ℕ, i < K →
      ∑ t ∈ Finset.range K, (C (g.coeff (K + i - t)) + C (g.coeff (K + i - t + p)) * X) *
        ∑ q ∈ Finset.range N, C ((r q).coeff t) * X ^ q = 0 := by
    intro i hi
    have e := expand (fun t => g.coeff (K + i - t)) (fun t => g.coeff (K + i - t + p))
      (fun q t => (r q).coeff t) N
    rw [e]
    have hC0 : ∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r 0).coeff t = 0 := by
      have h := hsys 0 ⟨i, hi⟩
      simpa only [lt_self_iff_false, if_false, add_zero, Fin.val_mk] using h
    have hstep : ∀ q : ℕ, ∑ t ∈ Finset.range K, g.coeff (K + i - t + p) * (r q).coeff t =
        -∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r (q + 1)).coeff t := by
      intro q
      have h := hsys (q + 1) ⟨i, hi⟩
      have hpos : 0 < q + 1 := Nat.succ_pos q
      simp only [if_pos hpos, Nat.add_sub_cancel, Finset.sum_add_distrib] at h
      linear_combination h
    have hCN : ∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r N).coeff t = 0 := by
      simp [hrN N le_rfl]
    have hsecond : ∑ q ∈ Finset.range N, X ^ (q + 1) * C (∑ t ∈ Finset.range K, g.coeff (K + i - t + p) * (r q).coeff t)
        = ∑ q ∈ Finset.range N, -(X ^ (q + 1) * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r (q + 1)).coeff t)) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hstep q, map_neg]
      ring
    rw [hsecond]
    have tel := Finset.sum_range_sub'
      (fun q => X ^ q * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r q).coeff t)) N
    have hsum : ∑ q ∈ Finset.range N, X ^ q * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r q).coeff t) +
        ∑ q ∈ Finset.range N, -(X ^ (q + 1) * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r (q + 1)).coeff t))
        = ∑ q ∈ Finset.range N, (X ^ q * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r q).coeff t) -
            X ^ (q + 1) * C (∑ t ∈ Finset.range K, g.coeff (K + i - t) * (r (q + 1)).coeff t)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hsum, tel, hC0, hCN]
    simp
  -- the vector of generating functions vanishes
  have hv : Matrix.mulVec (Matrix.of (fun (i t : Fin K) =>
      Polynomial.C (g.coeff (K + (i : ℕ) - (t : ℕ))) +
        Polynomial.C (g.coeff (K + (i : ℕ) - (t : ℕ) + p)) * (Polynomial.X : Polynomial (ZMod p))))
      (fun t : Fin K => ∑ q ∈ Finset.range N, C ((r q).coeff t) * X ^ q) = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range
      (fun t => (C (g.coeff (K + (i : ℕ) - t)) + C (g.coeff (K + (i : ℕ) - t + p)) * X) *
        ∑ q ∈ Finset.range N, C ((r q).coeff t) * X ^ q) K]
    exact core i i.isLt
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  by_cases hjN : N ≤ j
  · exact hrN j hjN
  · have hcoef : ∀ t : Fin K, (r j).coeff t = 0 := by
      intro t
      have h1 := congrArg (fun P => Polynomial.coeff P j) (congrFun hv0 t)
      simp only [Pi.zero_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at h1
      rw [Finset.sum_ite_eq] at h1
      have hjlt : j < N := not_le.mp hjN
      simpa [Finset.mem_range, hjlt] using h1
    ext n
    rw [Polynomial.coeff_zero]
    by_cases hn : n < K
    · exact hcoef ⟨n, hn⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hrK j) (not_lt.mp hn))

end MPP.Solutions.Bsd318
