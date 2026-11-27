import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp234
import MPP.Solutions.Pnp237
import MPP.Solutions.Pnp244

namespace MPP.Solutions.Pnp247

open MPP.PvsNP Turing

theorem main : ∀ a b : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    (∀ x : List Bool, b x ≠ []) →
    ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = w.getD ((a x).length % (b x).length) false := by
  intro a b ha hb hbne
  obtain ⟨p, hp, hpeq⟩ := MPP.Solutions.Pnp237.pairP ha hb
  obtain ⟨R, hR, hReq⟩ := MPP.Solutions.Pnp244.main
  have hh := MPP.Solutions.Pnp237.comp hp hR
  have hunary : ∀ x : List Bool, (R ∘ p) x = List.replicate ((R ∘ p) x).length true := by
    intro x
    simp [Function.comp_apply, hpeq, hReq (a x) (b x) (hbne x)]
  obtain ⟨L, hL, hLeq⟩ := MPP.Solutions.Pnp234.main (R ∘ p) hh hunary
  refine ⟨L, hL, fun x w => ?_⟩
  rw [hLeq x w]
  simp [Function.comp_apply, hpeq, hReq (a x) (b x) (hbne x)]

end MPP.Solutions.Pnp247
