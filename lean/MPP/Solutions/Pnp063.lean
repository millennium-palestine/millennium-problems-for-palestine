import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp037

namespace MPP.Solutions.Pnp063

open Computability Turing

theorem main : ∀ s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    ∀ k : ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, T z = s^[k] z := by
  intro s hs k
  induction k with
  | zero => exact ⟨id, MPP.Solutions.Pnp037.main, fun z => rfl⟩
  | succ k ih =>
    obtain ⟨T, hT, hTeq⟩ := ih
    obtain ⟨hT'⟩ := hT
    obtain ⟨hs'⟩ := hs
    refine ⟨s ∘ T, MPP.Solutions.Pnp006.main hT' hs', fun z => ?_⟩
    show s (T z) = s^[k + 1] z
    rw [hTeq z, Function.iterate_succ_apply']

end MPP.Solutions.Pnp063
