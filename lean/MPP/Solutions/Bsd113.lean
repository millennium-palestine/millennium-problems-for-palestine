import Mathlib

namespace MPP.Solutions.Bsd113

theorem main : ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (κ : G →+ H) (s : Set H) (D : Finset G), s.Finite →
    (∀ P : G, κ P ∈ s) → (∀ P Q : G, κ P = κ Q → ∃ d ∈ D, ∃ R : G, P = Q + d + 2 • R) →
    ∃ t : Finset G, ∀ P : G, ∃ Q ∈ t, ∃ R : G, P = Q + 2 • R := by
  intro G H _ _ κ s D hs hmem hfib
  classical
  have hpick : ∀ c : H, ∃ Q : G, (∃ P : G, κ P = c) → κ Q = c := by
    intro c
    by_cases h : ∃ P : G, κ P = c
    · obtain ⟨P, hP⟩ := h
      exact ⟨P, fun _ => hP⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose pick hpick using hpick
  refine ⟨(hs.toFinset.image pick ×ˢ D).image (fun z => z.1 + z.2), ?_⟩
  intro P
  have hpk : κ (pick (κ P)) = κ P := hpick (κ P) ⟨P, rfl⟩
  obtain ⟨d, hd, R, hR⟩ := hfib P (pick (κ P)) hpk.symm
  refine ⟨pick (κ P) + d, ?_, R, hR⟩
  rw [Finset.mem_image]
  refine ⟨(pick (κ P), d), Finset.mem_product.mpr ⟨?_, hd⟩, rfl⟩
  rw [Finset.mem_image]
  exact ⟨κ P, (Set.Finite.mem_toFinset hs).mpr (hmem P), rfl⟩

end MPP.Solutions.Bsd113
