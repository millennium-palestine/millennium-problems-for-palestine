import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp126
import MPP.Solutions.Pnp127

namespace MPP.Solutions.Pnp129

open MPP.PvsNP Turing

theorem main : ∀ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) →
    ∀ k : ℕ, ∃ T' : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T') ∧
      ∀ x : List Bool, T' x = (List.replicate k (T x)).flatten := by
  intro T hT k
  induction k with
  | zero =>
    obtain ⟨T0, hT0, hT0v⟩ := MPP.Solutions.Pnp126.main []
    exact ⟨T0, hT0, fun x => by simp [hT0v x]⟩
  | succ k ih =>
    obtain ⟨T1, hT1, hT1v⟩ := ih
    obtain ⟨T2, hT2, hT2v⟩ := MPP.Solutions.Pnp127.main T1 T hT1 hT
    exact ⟨T2, hT2, fun x => by
      rw [hT2v x, hT1v x]
      simp [List.replicate_succ', List.flatten_append]⟩

end MPP.Solutions.Pnp129
