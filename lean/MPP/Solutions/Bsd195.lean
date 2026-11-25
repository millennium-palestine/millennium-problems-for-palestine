import Mathlib

namespace MPP.Solutions.Bsd195

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime] (h : Polynomial (ZMod p)), h.natDegree < 2 * p →
    ∃ c d : Fin p → ZMod p, h = ∑ s : Fin p,
      Polynomial.X ^ (s : ℕ) * (Polynomial.C (c s) + Polynomial.C (d s) * Polynomial.X ^ p) := by
  intro p _ h hdeg
  refine ⟨fun s => h.coeff s, fun s => h.coeff ((s : ℕ) + p), ?_⟩
  have hterm : ∀ s : Fin p, (X : Polynomial (ZMod p)) ^ (s : ℕ) *
      (C (h.coeff s) + C (h.coeff ((s : ℕ) + p)) * X ^ p)
      = C (h.coeff s) * X ^ (s : ℕ) + C (h.coeff ((s : ℕ) + p)) * X ^ ((s : ℕ) + p) := by
    intro s
    ring
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  ext n
  simp only [coeff_add, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => if n = i then h.coeff i else 0) p,
    Fin.sum_univ_eq_sum_range (fun i => if n = i + p then h.coeff (i + p) else 0) p]
  rcases lt_or_ge n p with hn | hn
  · have h2 : ∑ i ∈ Finset.range p, (if n = i + p then h.coeff (i + p) else 0) = 0 :=
      Finset.sum_eq_zero (fun i _ => if_neg (by omega))
    rw [h2, add_zero, Finset.sum_ite_eq]
    simp [hn]
  · rcases lt_or_ge n (2 * p) with hn2 | hn2
    · have h1 : ∑ i ∈ Finset.range p, (if n = i then h.coeff i else 0) = 0 :=
        Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega))
      rw [h1, zero_add, Finset.sum_eq_single (n - p) (fun i _ hne => if_neg (by omega))
        (fun hm => absurd (Finset.mem_range.mpr (by omega)) hm), if_pos (by omega)]
      congr 1
      omega
    · have hz : h.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have h1 : ∑ i ∈ Finset.range p, (if n = i then h.coeff i else 0) = 0 :=
        Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega))
      have h2 : ∑ i ∈ Finset.range p, (if n = i + p then h.coeff (i + p) else 0) = 0 :=
        Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega))
      rw [h1, h2, hz, add_zero]

end MPP.Solutions.Bsd195
