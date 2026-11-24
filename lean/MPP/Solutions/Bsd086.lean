import Mathlib

namespace MPP.Solutions.Bsd086

theorem main : ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (κ : G →+ H) (s : Set H),
    s.Finite → (∀ P : G, κ P ∈ s) → (∀ P Q : G, κ P = κ Q → ∃ R : G, P = Q + 2 • R) →
      ∃ t : Finset G, ∀ P : G, ∃ Q ∈ t, ∃ R : G, P = Q + 2 • R := by
  intro G H _ _ κ s hs him hker
  classical
  -- a preimage for every value that has one
  have key : ∀ c : H, ∃ Q : G, (∃ P : G, κ P = c) → κ Q = c := by
    intro c
    by_cases h : ∃ P : G, κ P = c
    · obtain ⟨P, hP⟩ := h
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose pick hpick using key
  refine ⟨hs.toFinset.image pick, ?_⟩
  intro P
  have hκ : κ P = κ (pick (κ P)) := (hpick (κ P) ⟨P, rfl⟩).symm
  obtain ⟨R, hR⟩ := hker P (pick (κ P)) hκ
  exact ⟨pick (κ P), Finset.mem_image.mpr ⟨κ P, hs.mem_toFinset.mpr (him P), rfl⟩, R, hR⟩

end MPP.Solutions.Bsd086
