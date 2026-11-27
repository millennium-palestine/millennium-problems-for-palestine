import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp037
import MPP.Solutions.Pnp081
import MPP.Solutions.Pnp234
import MPP.Solutions.Pnp237
import MPP.Solutions.Pnp260

namespace MPP.Solutions.Pnp261

open MPP.PvsNP Turing

theorem main : ∀ a b c : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) c) →
    ∃ L : Lang, InP L ∧ ∀ x w : List Bool,
      L (pair x w) = w.getD ((a x).length * (b x).length + (c x).length) false := by
  intro a b c ha hb hc
  obtain ⟨F, hF, hFeq⟩ := MPP.Solutions.Pnp260.main a b c ha hb hc
  obtain ⟨Y, hY, hYeq⟩ := MPP.Solutions.Pnp026.main id F MPP.Solutions.Pnp037.main hF
  obtain ⟨r, hr, hreq⟩ := MPP.Solutions.Pnp081.main
  obtain ⟨e, he, heq⟩ := MPP.Solutions.Pnp025.main
  have hG := MPP.Solutions.Pnp237.comp (MPP.Solutions.Pnp237.comp hY hr) he
  have hunary : ∀ x : List Bool,
      (e ∘ (r ∘ Y)) x = List.replicate ((e ∘ (r ∘ Y)) x).length true := by
    intro x
    simp [Function.comp_apply, hYeq, hreq, heq, hFeq, List.map_replicate]
  obtain ⟨L, hL, hLeq⟩ := MPP.Solutions.Pnp234.main (e ∘ (r ∘ Y)) hG hunary
  refine ⟨L, hL, fun x w => ?_⟩
  rw [hLeq x w]
  simp [Function.comp_apply, hYeq, hreq, heq, hFeq, List.map_replicate]

end MPP.Solutions.Pnp261
