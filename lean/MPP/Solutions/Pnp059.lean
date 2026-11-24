import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp059

open MPP.PvsNP

theorem main : ∀ (V : Lang) (x : List Bool) (N : ℕ) (E : List Bool → Bool),
    (∀ u : List Bool, E u = true ↔
      ∃ w : List Bool, w.length = N ∧ (∃ t : List Bool, w = u ++ t) ∧ V (pair x w) = true) →
    (∃ w : List Bool, w.length = N ∧ V (pair x w) = true) →
    E [] = true ∧
      ∀ u : List Bool, u.length < N → E u = true → E (u ++ [false]) = true ∨ E (u ++ [true]) = true := by
  intro V x N E hE hw
  obtain ⟨w0, hl0, hv0⟩ := hw
  refine ⟨(hE []).2 ⟨w0, hl0, ⟨w0, by simp⟩, hv0⟩, ?_⟩
  intro u hlt hEu
  obtain ⟨w, hwl, ⟨t, rfl⟩, hv⟩ := (hE u).1 hEu
  cases t with
  | nil =>
    simp at hwl
    omega
  | cons b t' =>
    cases b
    · left
      exact (hE (u ++ [false])).2 ⟨u ++ false :: t', hwl, ⟨t', by simp⟩, hv⟩
    · right
      exact (hE (u ++ [true])).2 ⟨u ++ true :: t', hwl, ⟨t', by simp⟩, hv⟩

end MPP.Solutions.Pnp059
