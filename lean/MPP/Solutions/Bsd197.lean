import Mathlib

namespace MPP.Solutions.Bsd197

theorem main : ∀ (K : Type) [Field K] (f : Polynomial K), f ≠ 0 →
    Set.ncard {x : K | f.eval x = 0} ≤ f.natDegree := by
  intro K _ f hf
  classical
  have hset : {x : K | f.eval x = 0} = ↑f.roots.toFinset := by
    ext x
    simp [Polynomial.mem_roots hf]
  rw [hset, Set.ncard_coe_finset]
  calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f

end MPP.Solutions.Bsd197
