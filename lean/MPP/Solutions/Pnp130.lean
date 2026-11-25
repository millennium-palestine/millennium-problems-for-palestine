import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp052
import MPP.Solutions.Pnp116

namespace MPP.Solutions.Pnp130

open MPP.PvsNP Computability Turing

/-- Windowed-witness language: a witness of length at most |x| makes every window of k + 1
consecutive symbols of x ++ w satisfy g. It is in NP, with the verifier given by the all-windows
test of pnp-116 on the concatenation map of pnp-052. -/
theorem main : ∀ g : Lang, InP g → ∀ k : ℕ, ∃ S : Lang, InNP S ∧ ∀ x : List Bool, S x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ∧
      ∀ i : ℕ, i + (k + 1) ≤ (x ++ w).length → g (((x ++ w).drop i).take (k + 1)) = true := by
  classical
  intro g hg k
  obtain ⟨C, ⟨hC⟩, hCeq⟩ := MPP.Solutions.Pnp052.main
  have hW := MPP.Solutions.Pnp116.main g hg k
  have hV := MPP.Solutions.Pnp008.main _ C hW hC
  refine ⟨fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧
      ∀ i : ℕ, i + (k + 1) ≤ (x ++ w).length → g (((x ++ w).drop i).take (k + 1)) = true), ?_, ?_⟩
  · refine ⟨_, hV, Polynomial.X, fun x => ?_⟩
    simp only [Polynomial.eval_X, decide_eq_true_iff, hCeq]
    refine exists_congr fun w => and_congr_right fun _ => ⟨fun h i _ hi => h i hi, fun h i hi => h i (by omega) hi⟩
  · intro x
    simp
end MPP.Solutions.Pnp130
