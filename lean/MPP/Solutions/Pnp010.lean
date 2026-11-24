import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp009

namespace MPP.Solutions.Pnp010

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- One stack, one label. Pop the first bit into the state, pop the second and
disjoin it into the state, push the state back, halt. -/
abbrev orMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.getD false)
    (pop () (fun s o => s || o.getD false) (push () (fun v => v) (load (fun _ => false) halt)))

theorem orComp : Nonempty (TM2ComputableInPolyTime
    (fun p : Bool × Bool => [p.1, p.2]) encodeBool (fun p : Bool × Bool => p.1 || p.2)) := by
  refine ⟨{ tm := orMachine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := 1
            outputsFun := fun p => ?_ }⟩
  refine ⟨⟨1, ?_⟩, ?_⟩
  · rcases p with ⟨a, b⟩
    cases a <;> cases b <;> rfl
  · simp

theorem main : ∀ L M : Lang, InP L → InP M → InP (fun x => L x || M x) := by
  intro L M hL hM
  obtain ⟨h9⟩ := MPP.Solutions.Pnp009.main L M hL hM
  obtain ⟨hor⟩ := orComp
  obtain ⟨c⟩ := MPP.Solutions.Pnp006.main h9 hor
  exact Nonempty.intro c

end MPP.Solutions.Pnp010
