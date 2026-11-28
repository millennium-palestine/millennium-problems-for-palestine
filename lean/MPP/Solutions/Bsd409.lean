import Mathlib

namespace MPP.Solutions.Bsd409

open Polynomial

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ),
    Odd m → (m : K) ≠ 0 → Squarefree (W.preΨ' m) →
      Nat.card {x : K // (W.preΨ' m).eval x = 0} = (m ^ 2 - 1) / 2 := by
  intro K _ _ W _ m hodd hm hsq
  classical
  have hdeg : (W.preΨ' m).natDegree = (m ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ' hm, if_neg (Nat.not_even_iff_odd.mpr hodd)]
  have hne : W.preΨ' m ≠ 0 := W.preΨ'_ne_zero hm
  have hsep : (W.preΨ' m).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hsplit : Splits ((W.preΨ' m).map (algebraMap K K)) := IsAlgClosed.splits_domain _
  have hcard := card_rootSet_eq_natDegree (K := K) hsep hsplit
  have hequiv : {x : K // (W.preΨ' m).eval x = 0} ≃ (W.preΨ' m).rootSet K :=
    Equiv.subtypeEquivRight fun x => by
      rw [mem_rootSet_of_ne hne, aeval_def, Algebra.algebraMap_self, eval₂_id]
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, hcard, hdeg]

end MPP.Solutions.Bsd409
