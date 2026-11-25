import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp116

namespace MPP.Solutions.Pnp153

open MPP.PvsNP

/-- The witness is never needed. Every window of `x ++ w` that lies inside `x` is a window of `x`
itself, and the empty suffix `w = []` checks exactly those windows. So the windowed-witness language
equals the language of pnp-116 on `x`, which is polynomial-time by pnp-116. -/
theorem main : ∀ g : Lang, InP g → ∀ k : ℕ, ∃ S : Lang, InP S ∧ ∀ x : List Bool, S x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ∧
      ∀ i : ℕ, i + (k + 1) ≤ (x ++ w).length → g (((x ++ w).drop i).take (k + 1)) = true := by
  intro g hg k
  refine ⟨fun x => decide (∀ i < x.length, i + (k + 1) ≤ x.length → g ((x.drop i).take (k + 1)) = true),
    MPP.Solutions.Pnp116.main g hg k, ?_⟩
  intro x
  dsimp only
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    intro i hi
    rw [List.append_nil] at hi ⊢
    exact hx i (by omega) hi
  · rintro ⟨w, -, hw⟩ i - hi
    have hwin : ((x ++ w).drop i).take (k + 1) = (x.drop i).take (k + 1) := by
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    have h := hw i (by simp only [List.length_append]; omega)
    rwa [hwin] at h

end MPP.Solutions.Pnp153
