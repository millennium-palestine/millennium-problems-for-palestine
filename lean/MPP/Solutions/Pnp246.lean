import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp234
import MPP.Solutions.Pnp237
import MPP.Solutions.Pnp245

namespace MPP.Solutions.Pnp246

open MPP.PvsNP Turing

theorem main : ∀ a b : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = w.getD ((a x).length - (b x).length) false := by
  intro a b ha hb
  obtain ⟨p, hp, hpeq⟩ := MPP.Solutions.Pnp237.pairP ha hb
  obtain ⟨S, hS, hSeq⟩ := MPP.Solutions.Pnp245.main
  have hh := MPP.Solutions.Pnp237.comp hp hS
  have hunary : ∀ x : List Bool, (S ∘ p) x = List.replicate ((S ∘ p) x).length true := by
    intro x
    simp [Function.comp_apply, hpeq, hSeq]
  obtain ⟨L, hL, hLeq⟩ := MPP.Solutions.Pnp234.main (S ∘ p) hh hunary
  refine ⟨L, hL, fun x w => ?_⟩
  rw [hLeq x w]
  simp [Function.comp_apply, hpeq, hSeq]

end MPP.Solutions.Pnp246
