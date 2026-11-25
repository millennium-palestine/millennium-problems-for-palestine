import Mathlib

namespace MPP.Solutions.Bsd216

theorem main : ∀ (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (m : ℕ),
    Odd m → (m : K) ≠ 0 → (W.preΨ' m).roots.toFinset.card ≤ (m ^ 2 - 1) / 2 := by
  intro K _ _ W m hodd hm
  have hdeg : (W.preΨ' m).natDegree = (m ^ 2 - if Even m then 4 else 1) / 2 :=
    W.natDegree_preΨ' hm
  have hodd' : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
  calc (W.preΨ' m).roots.toFinset.card
      ≤ Multiset.card (W.preΨ' m).roots := Multiset.toFinset_card_le _
    _ ≤ (W.preΨ' m).natDegree := Polynomial.card_roots' _
    _ = (m ^ 2 - 1) / 2 := by rw [hdeg, if_neg hodd']

end MPP.Solutions.Bsd216
