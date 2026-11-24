import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp007

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- One stack, one label. Pop the first bit into the state, pop the second and
conjoin it into the state, push the state back, halt. -/
abbrev andMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.getD false)
    (pop () (fun s o => s && o.getD false) (push () (fun v => v) (load (fun _ => false) halt)))

theorem main : Nonempty (TM2ComputableInPolyTime
    (fun p : Bool × Bool => [p.1, p.2]) encodeBool (fun p : Bool × Bool => p.1 && p.2)) := by
  refine ⟨{ tm := andMachine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := fun p => ?_ }⟩
  refine ⟨⟨1, ?_⟩, ?_⟩
  · rcases p with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · simp

end MPP.Solutions.Pnp007
