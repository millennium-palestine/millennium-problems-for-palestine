import Mathlib

namespace MPP.Solutions.Bsd377

theorem main : ∀ (p : ℕ) [Fact p.Prime] (a b : ZMod p),
    (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card ≤ 3 := by
  intro p _ a b
  set f : Polynomial (ZMod p) := Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b with hf
  have hdeg : f.natDegree ≤ 3 := by
    rw [hf]
    compute_degree!
  have hne : f ≠ 0 := by
    intro h
    have h3 : f.coeff 3 = 1 := by
      rw [hf]
      simp [Polynomial.coeff_X_pow]
    rw [h] at h3
    simp at h3
  have hsub : Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0) ⊆ f.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, hf]
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul] using hx
  calc (Finset.univ.filter (fun x : ZMod p => x ^ 3 + a * x + b = 0)).card
      ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ ≤ 3 := hdeg

end MPP.Solutions.Bsd377
