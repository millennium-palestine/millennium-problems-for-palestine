import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp065

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- Two stacks: `false` is the input, `true` the output. The state is `(ans, nonEmpty)`:
`ans` is `none` until a symbol is read, and `nonEmpty` records whether the last pop of the input
returned a symbol. The machine pops the input symbol by symbol. When the input is empty it pushes
`!ans.isSome` (true exactly when nothing was read) onto the output, then pops the empty input once
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
  m _ := pop false (fun v o => (v.1.or o, o.isSome))
    (branch (fun v => v.2) (goto fun _ => ())
      (push true (fun v => !v.1.isSome) (pop false (fun _ _ => (none, false)) halt)))

/-- Configuration with the label running, state `v`, input `l` and empty output. -/
def cfgOf (l : List Bool) (v : Option Bool × Bool) : machine.Cfg :=
  ⟨some (), v, fun k => cond k [] l⟩

theorem step_cons (b : Bool) (l : List Bool) (v : Option Bool × Bool) :
    machine.step (cfgOf (b :: l) v) = some (cfgOf l (v.1.or (some b), true)) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem step_nil (v : Option Bool × Bool) :
    machine.step (cfgOf [] v) =
      some ⟨none, (none, false), fun k => cond k [!v.1.isSome] []⟩ := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem run (l : List Bool) (v : Option Bool × Bool) :
    (flip bind machine.step)^[l.length + 1] (some (cfgOf l v)) =
      some ⟨none, (none, false), fun k => cond k [v.1.isNone && l.isEmpty] []⟩ := by
  induction l generalizing v with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    show machine.step (cfgOf [] v) = _
    rw [step_nil v]
    simp
  | cons b l ih =>
    rw [List.length_cons, Nat.add_succ, Function.iterate_succ_apply]
    rw [show (flip bind machine.step) (some (cfgOf (b :: l) v)) =
        some (cfgOf l (v.1.or (some b), true)) from step_cons b l v]
    rw [ih (v.1.or (some b), true)]
    simp

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

theorem emptyInP : InP (fun z : List Bool => z.isEmpty) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨a.length + 1, ?_⟩, ?_⟩
  · show (flip bind machine.step)^[a.length + 1]
        (some (initList machine (List.map (Equiv.refl Bool).invFun (id a)))) =
      Option.map (haltList machine)
        (some (List.map (Equiv.refl Bool).invFun (encodeBool a.isEmpty)))
    have h : List.map (Equiv.refl Bool).invFun (id a) = a := by simp
    have h2 : List.map (Equiv.refl Bool).invFun (encodeBool a.isEmpty) = [a.isEmpty] := by
      simp [encodeBool]
    simp only [h, h2]
    rw [init_eq, run, Option.map_some, halt_eq]
    simp
  · simp

theorem main : ∃ Z : Lang, InP Z ∧ ∀ z : List Bool, Z z = true ↔ z = [] :=
  ⟨fun z => z.isEmpty, emptyInP, fun z => by simp⟩

end MPP.Solutions.Pnp065
