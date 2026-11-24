import Mathlib
import MPP.Solutions.Bsd027

namespace MPP.Solutions.Bsd039

theorem main : ∀ (G : Type) [AddCommGroup G] (h : G → ℝ) (C D : ℝ),
    (∀ P : G, 0 ≤ h P) → (∀ P : G, h (-P) = h P) →
    (∀ P Q : G, h (P + Q) ≤ 2 * h P + 2 * h Q + C) →
    (∀ P : G, 4 * h P - D ≤ h (2 • P)) →
    (∀ M : ℝ, {P : G | h P ≤ M}.Finite) →
    (∃ s : Finset G, ∀ P : G, ∃ Q ∈ s, ∃ R : G, P = Q + 2 • R) →
    AddGroup.FG G := by
  intro G _ h C D h0 hneg hadd hdbl hfin hrep
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = max 0 (C / 3) := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by
    rw [hk]
    exact le_max_left _ _
  have hkC : C ≤ 3 * k := by
    have := le_max_right 0 (C / 3)
    rw [hk]
    linarith
  refine MPP.Solutions.Bsd027.main G (fun P => h P + k) (D + 3 * k) ?_ ?_ ?_ ?_ ?_ hrep
  · intro P
    linarith [h0 P]
  · intro P
    rw [hneg P]
  · intro P Q
    linarith [hadd P Q]
  · intro P
    linarith [hdbl P]
  · intro M
    refine (hfin (M - k)).subset fun P hP => ?_
    simp only [Set.mem_setOf_eq] at hP ⊢
    linarith

end MPP.Solutions.Bsd039
