import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp003

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- One stack (input and output at once), one label, one bit of state. The machine
pops the input symbol by symbol, recording in its state whether a symbol was popped;
once the stack is empty it pushes `true` and halts. -/
abbrev machine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := pop () (fun _ o => o.isSome)
    (branch id (goto fun _ => ()) (push () (fun _ => true) halt))

/-- Configuration with the label running and the stack holding `l`. -/
def cfgOf (l : List Bool) (v : Bool) : machine.Cfg :=
  ⟨some (), v, fun _ => l⟩

theorem step_cons (b : Bool) (l : List Bool) (v : Bool) :
    machine.step (cfgOf (b :: l) v) = some (cfgOf l true) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  all_goals rfl

theorem step_nil (v : Bool) :
    machine.step (cfgOf [] v) = some ⟨none, false, fun _ => [true]⟩ := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  all_goals rfl

theorem run (l : List Bool) (v : Bool) :
    (flip bind machine.step)^[l.length + 1] (some (cfgOf l v)) =
      some ⟨none, false, fun _ => [true]⟩ := by
  induction l generalizing v with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    exact step_nil v
  | cons b l ih =>
    rw [List.length_cons, Nat.add_succ, Function.iterate_succ_apply]
    exact ih true

theorem init_eq (a : List Bool) : initList machine a = cfgOf a false := by
  simp [initList, cfgOf, machine]

theorem halt_eq : haltList machine [true] = ⟨none, false, fun _ => [true]⟩ := by
  simp [haltList, machine]

theorem main : InP (fun _ => true) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨a.length + 1, ?_⟩, ?_⟩
  · show (flip bind machine.step)^[a.length + 1]
        (some (initList machine (List.map (Equiv.refl Bool).invFun (id a)))) =
      Option.map (haltList machine) (some (List.map (Equiv.refl Bool).invFun (encodeBool true)))
    have h : List.map (Equiv.refl Bool).invFun (id a) = a := by simp
    have h2 : List.map (Equiv.refl Bool).invFun (encodeBool true) = [true] := by
      simp [encodeBool]
    simp only [h, h2]
    rw [init_eq, run]
    exact congrArg some halt_eq.symm
  · simp

end MPP.Solutions.Pnp003
