import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp126
import MPP.Solutions.Pnp127

namespace MPP.Solutions.Pnp128

open MPP.PvsNP Turing

theorem main : ∀ k : ℕ, ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ x : List Bool, T x = (List.replicate k x).flatten := by
  intro k
  induction k with
  | zero =>
    obtain ⟨T, hT, hTv⟩ := MPP.Solutions.Pnp126.main []
    exact ⟨T, hT, fun x => by simp [hTv x]⟩
  | succ k ih =>
    obtain ⟨T, hT, hTv⟩ := ih
    obtain ⟨T', hT', hT'v⟩ := MPP.Solutions.Pnp127.main T id hT MPP.Solutions.Pnp037.main
    exact ⟨T', hT', fun x => by
      rw [hT'v x, hTv x]
      simp [List.replicate_succ', List.flatten_append]⟩

end MPP.Solutions.Pnp128
