import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp002
import MPP.Solutions.Pnp003

namespace MPP.Solutions.Pnp042

open MPP.PvsNP Turing

theorem main : ¬ (∀ L : Lang, InNP L → ∃ f : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) ∧
      ∀ x, L x = (fun _ => false) (f x)) := by
  intro h
  obtain ⟨f, _, hf⟩ := h (fun _ => true) (MPP.Solutions.Pnp002.main _ MPP.Solutions.Pnp003.main)
  have h0 := hf []
  simp at h0

end MPP.Solutions.Pnp042
