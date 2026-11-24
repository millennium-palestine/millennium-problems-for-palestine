import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp013

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- Two stacks: `false` is the input, `true` the output. The state is `(ans, nonEmpty)`:
`ans` is the first symbol read (`none` before any symbol is read) and `nonEmpty` records whether
the last pop of the input returned a symbol. The machine pops the input symbol by symbol. When
the input is empty it pushes `ans` (or `false`) onto the output, then pops the (empty) input once
more so that the state returns to `initialState`, as `haltList` requires. -/
abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool × Bool
  initialState := (none, false)
  m _ := pop false (fun v o => (some (v.1.getD (o.getD false)), o.isSome))
    (branch (fun v => v.2) (goto fun _ => ())
      (push true (fun v => v.1.getD false) (pop false (fun _ _ => (none, false)) halt)))

/-- Configuration with the label running, state `v`, input `l` and empty output. -/
def cfgOf (l : List Bool) (v : Option Bool × Bool) : machine.Cfg :=
  ⟨some (), v, fun k => cond k [] l⟩

theorem step_cons (b : Bool) (l : List Bool) (v : Option Bool × Bool) :
    machine.step (cfgOf (b :: l) v) = some (cfgOf l (some (v.1.getD b), true)) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem step_nil (v : Option Bool × Bool) :
    machine.step (cfgOf [] v) =
      some ⟨none, (none, false), fun k => cond k [v.1.getD false] []⟩ := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem run (l : List Bool) (v : Option Bool × Bool) :
    (flip bind machine.step)^[l.length + 1] (some (cfgOf l v)) =
      some ⟨none, (none, false), fun k => cond k [v.1.getD (l.headD false)] []⟩ := by
  induction l generalizing v with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    exact step_nil v
  | cons b l ih =>
    rw [List.length_cons, Nat.add_succ, Function.iterate_succ_apply]
    rw [show (flip bind machine.step) (some (cfgOf (b :: l) v)) =
        some (cfgOf l (some (v.1.getD b), true)) from step_cons b l v]
    exact ih (some (v.1.getD b), true)

theorem init_eq (a : List Bool) :
    initList machine a = cfgOf a (none, false) := by
  simp [initList, cfgOf, machine]
  congr 1
  funext k
  cases k <;> simp

theorem halt_eq (b : Bool) :
    haltList machine [b] = ⟨none, (none, false), fun k => cond k [b] []⟩ := by
  simp [haltList, machine]
  congr 1
  funext k
  cases k <;> simp

theorem main : InP (fun x => x.headD false) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨a.length + 1, ?_⟩, ?_⟩
  · show (flip bind machine.step)^[a.length + 1]
        (some (initList machine (List.map (Equiv.refl Bool).invFun (id a)))) =
      Option.map (haltList machine)
        (some (List.map (Equiv.refl Bool).invFun (encodeBool (a.headD false))))
    have h : List.map (Equiv.refl Bool).invFun (id a) = a := by simp
    have h2 : List.map (Equiv.refl Bool).invFun (encodeBool (a.headD false)) =
        [a.headD false] := by
      simp [encodeBool]
    simp only [h, h2]
    rw [init_eq, run, Option.map_some, halt_eq]
    rfl
  · simp

end MPP.Solutions.Pnp013
