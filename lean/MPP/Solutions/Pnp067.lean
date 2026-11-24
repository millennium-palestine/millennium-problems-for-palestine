import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp033
import MPP.Solutions.Pnp037

namespace MPP.Solutions.Pnp067

open MPP.PvsNP Turing

theorem main : (∀ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ z : List Bool, (s z).length = z.length + 1) →
    ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, ∀ k : ℕ, T (pair z (List.replicate k false)) = s^[k] z) →
  ∀ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ z : List Bool, (s z).length = z.length + 1) →
    ∀ p : Polynomial ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, T z = s^[p.eval z.length] z := by
  intro H s hs hlen p
  obtain ⟨g, hg, hgdef⟩ := MPP.Solutions.Pnp033.main p
  obtain ⟨h, hh, hhdef⟩ := MPP.Solutions.Pnp026.main id g MPP.Solutions.Pnp037.main hg
  obtain ⟨T, hT, hTdef⟩ := H s hs hlen
  obtain ⟨hh'⟩ := hh
  obtain ⟨hT'⟩ := hT
  refine ⟨T ∘ h, MPP.Solutions.Pnp006.main hh' hT', ?_⟩
  intro z
  simp only [Function.comp_apply, hhdef, id, hgdef]
  exact hTdef z _

end MPP.Solutions.Pnp067
