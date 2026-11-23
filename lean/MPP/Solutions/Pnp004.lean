import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006

namespace MPP.Solutions.Pnp004

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- One stack, one label: pop the input bit into the state, push its negation, reset the
state and halt. -/
abbrev negMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.getD false) (push () (fun v => !v) (load (fun _ => false) halt))

theorem negComp : Nonempty (TM2ComputableInPolyTime encodeBool encodeBool (fun b : Bool => !b)) := by
  refine ⟨{ tm := negMachine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨1, ?_⟩, ?_⟩
  · cases a <;> rfl
  · simp

theorem main : ∀ L : Lang, InP L → InP (fun x => !L x) := by
  intro L hL
  obtain ⟨h1⟩ := hL
  obtain ⟨h2⟩ := negComp
  exact MPP.Solutions.Pnp006.main h1 h2

end MPP.Solutions.Pnp004
