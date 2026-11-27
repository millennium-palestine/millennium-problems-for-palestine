import Mathlib

namespace MPP.Solutions.Bsd373

theorem det_natDegree_le_of_upper {R : Type*} [CommRing R] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (Polynomial R))
    (hdeg : ∀ r c, (M r c).natDegree ≤ 1)
    (hY : ∀ r c : Fin n, (c : ℕ) ≤ (r : ℕ) → (M r c).natDegree = 0) :
    M.det.natDegree ≤ n - 1 := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · obtain ⟨i0, hi0⟩ : ∃ i : Fin n, (i : ℕ) ≤ (σ i : ℕ) := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      have hsum : ∑ i : Fin n, (σ i : ℕ) = ∑ i : Fin n, (i : ℕ) :=
        Equiv.sum_comp σ (fun i => (i : ℕ))
      have hlt : ∑ i : Fin n, (σ i : ℕ) < ∑ i : Fin n, (i : ℕ) :=
        Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i _ => hcon i)
      omega
    have h0 : (M (σ i0) i0).natDegree = 0 := hY (σ i0) i0 hi0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), h0, zero_add]
    calc ∑ i ∈ Finset.univ.erase i0, (M (σ i) i).natDegree
        ≤ ∑ i ∈ Finset.univ.erase i0, 1 := Finset.sum_le_sum (fun i _ => hdeg _ _)
      _ = n - 1 := by simp [Finset.card_erase_of_mem]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p), 2 < p →
    ∀ g : Polynomial (ZMod p),
      g = (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) ^ ((p - 1) / 2) →
      (Matrix.of (fun (i t : Fin ((p - 1) / 2)) =>
        Polynomial.C (g.coeff ((p - 1) / 2 + (i : ℕ) - (t : ℕ))) +
          Polynomial.C (g.coeff ((p - 1) / 2 + (i : ℕ) - (t : ℕ) + p)) *
            (Polynomial.X : Polynomial (ZMod p)))).det.natDegree ≤ (p - 1) / 2 - 1 := by
  intro p _ a b hp g hg
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcubic : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b :
      Polynomial (ZMod p)).natDegree ≤ 3 := by
    compute_degree!
  have hdegg : g.natDegree ≤ 3 * ((p - 1) / 2) := by
    rw [hg]
    calc _ ≤ (p - 1) / 2 * (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X +
          Polynomial.C b : Polynomial (ZMod p)).natDegree := Polynomial.natDegree_pow_le
      _ ≤ (p - 1) / 2 * 3 := Nat.mul_le_mul_left _ hcubic
      _ = 3 * ((p - 1) / 2) := Nat.mul_comm _ _
  apply det_natDegree_le_of_upper
  · intro r c
    simp only [Matrix.of_apply]
    compute_degree!
  · intro r c hrc
    have h0 : g.coeff ((p - 1) / 2 + (r : ℕ) - (c : ℕ) + p) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    simp only [Matrix.of_apply, h0]
    simp

end MPP.Solutions.Bsd373
