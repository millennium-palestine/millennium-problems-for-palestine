import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp008
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp029
import MPP.Solutions.Pnp052
import MPP.Solutions.Pnp122
import MPP.Solutions.Pnp137

namespace MPP.Solutions.Pnp140

open MPP.PvsNP Computability Turing

/-- Windowed-witness language with windows as wide as the input. The verifier maps the pair
`(x, w)` to the window list of `x ++ w` of width `|x| + 1` (pnp-137 with the unary count of `x`),
and tests that every bit is true (pnp-122). -/
theorem main : ∀ g : Lang, InP g → ∃ S : Lang, InNP S ∧ ∀ x : List Bool, S x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ∧
      ∀ i : ℕ, i + (x.length + 1) ≤ (x ++ w).length →
        g (((x ++ w).drop i).take (x.length + 1)) = true := by
  classical
  intro g hg
  obtain ⟨C, ⟨hC⟩, hCeq⟩ := MPP.Solutions.Pnp052.main
  obtain ⟨d, ⟨hd⟩, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨Lg, ⟨hLg⟩, hLgeq⟩ := MPP.Solutions.Pnp029.main
  obtain ⟨F, ⟨hF⟩, hFeq⟩ := MPP.Solutions.Pnp137.main g hg
  -- the input (x, w) becomes the pair (x ++ w, replicate |x| false)
  obtain ⟨M, ⟨hM⟩, hMeq⟩ :=
    MPP.Solutions.Pnp026.main C (Lg ∘ d) ⟨hC⟩ (MPP.Solutions.Pnp006.main hd hLg)
  have hMx : ∀ x w : List Bool, M (pair x w) = pair (x ++ w) (List.replicate x.length false) := by
    intro x w
    simp only [hMeq, Function.comp_apply, hCeq, hdeq, hLgeq]
  obtain ⟨hFM⟩ := MPP.Solutions.Pnp006.main hM hF
  -- the verifier: every window bit is true
  have hV : InP (fun z => decide (∀ b ∈ (F ∘ M) z, b = true)) :=
    MPP.Solutions.Pnp008.main _ (F ∘ M) MPP.Solutions.Pnp122.main hFM
  -- every bit of the window list is true iff every window satisfies g
  have hall : ∀ (N : ℕ) (f : Fin N → Bool),
      decide (∀ b ∈ List.ofFn f, b = true) = true ↔ ∀ i : Fin N, f i = true := by
    intro N f
    simp [List.mem_ofFn]
  refine ⟨fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧
      decide (∀ b ∈ (F ∘ M) (pair x w), b = true) = true), ?_, ?_⟩
  · refine ⟨_, hV, Polynomial.X, fun x => ?_⟩
    simp only [Polynomial.eval_X, decide_eq_true_iff]
  · intro x
    rw [decide_eq_true_iff]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    rw [Function.comp_apply, hMx, hFeq, List.length_replicate, hall]
    constructor
    · intro h i hi
      have hlt : i < (x ++ w).length + 1 - (x.length + 1) := by
        simp only [List.length_append] at hi ⊢
        omega
      simpa using h ⟨i, hlt⟩
    · intro h i
      have hi : (i : ℕ) + (x.length + 1) ≤ (x ++ w).length := by
        have := i.isLt
        simp only [List.length_append] at this ⊢
        omega
      simpa using h i hi

end MPP.Solutions.Pnp140
