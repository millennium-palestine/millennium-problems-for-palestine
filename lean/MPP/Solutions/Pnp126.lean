import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp030
import MPP.Solutions.Pnp125

namespace MPP.Solutions.Pnp126

open MPP.PvsNP Turing

theorem main : ∀ c : List Bool, ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ x : List Bool, T x = c := by
  intro c
  induction c using List.reverseRecOn with
  | nil =>
    obtain ⟨g, hg, hgv⟩ := MPP.Solutions.Pnp030.main 0
    exact ⟨g, hg, fun x => by simp [hgv x]⟩
  | append_singleton c b ih =>
    obtain ⟨T, hT, hTv⟩ := ih
    obtain ⟨T', hT', hT'v⟩ := MPP.Solutions.Pnp125.main T b hT
    exact ⟨T', hT', fun x => by rw [hT'v x, hTv x]⟩

end MPP.Solutions.Pnp126
