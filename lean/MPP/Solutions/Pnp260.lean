import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp031
import MPP.Solutions.Pnp032
import MPP.Solutions.Pnp237

namespace MPP.Solutions.Pnp260

open MPP.PvsNP Turing

theorem main : ∀ a b c : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) c) →
    ∃ F : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) F) ∧
      ∀ z : List Bool, F z = List.replicate ((a z).length * (b z).length + (c z).length) false := by
  intro a b c ha hb hc
  obtain ⟨p, hp, hpeq⟩ := MPP.Solutions.Pnp237.pairP ha hb
  obtain ⟨M, hM, hMeq⟩ := MPP.Solutions.Pnp032.main
  obtain ⟨r, hr, hreq⟩ := MPP.Solutions.Pnp237.pairP (MPP.Solutions.Pnp237.comp hp hM) hc
  obtain ⟨E, hE, hEeq⟩ := MPP.Solutions.Pnp031.main
  refine ⟨E ∘ r, MPP.Solutions.Pnp237.comp hr hE, fun z => ?_⟩
  simp [Function.comp_apply, hreq, hEeq, hMeq, hpeq]

end MPP.Solutions.Pnp260
