import Mathlib

namespace MPP.Solutions.Bsd313

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K),
    (5 : K) ≠ 0 → Squarefree (W.preΨ' 5) →
    ∃ R : Finset K, R.card = 12 ∧ ∀ x ∈ R, (W.preΨ' 5).eval x = 0 := by
  intro K _ _ _ W h5 hsq
  -- the 5-division polynomial has degree 12
  have hdeg : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' (n := 5) (by exact_mod_cast h5)]
    norm_num [Nat.even_iff]
  have hf0 : W.preΨ' 5 ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  -- squarefree gives twelve distinct roots over an algebraically closed field
  have hsep : (W.preΨ' 5).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hcard : (W.preΨ' 5).roots.toFinset.card = 12 := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hdeg]
  refine ⟨(W.preΨ' 5).roots.toFinset, hcard, fun x hx => ?_⟩
  exact (Polynomial.mem_roots hf0).mp (Multiset.mem_toFinset.mp hx)

end MPP.Solutions.Bsd313
