import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp122

open MPP.PvsNP Computability Turing Turing.TM2.Stmt

/-- Two stacks: `false` is the input, `true` the output. The state is `(ok, nonEmpty)`: `ok` is
true while every symbol read so far is true, and `nonEmpty` records whether the last pop of the
input returned a symbol. The machine pops the input one symbol at a time. When the input is empty
it pushes `ok` onto the output, then pops the (empty) input once more so that the state returns to
`initialState`, as `haltList` requires. -/
abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (true, false)
  m _ := pop false (fun v o => (v.1 && o.getD true, o.isSome))
    (branch (fun v => v.2) (goto fun _ => ())
      (push true (fun v => v.1) (pop false (fun _ _ => (true, false)) halt)))

/-- Configuration with the label running, state `v`, input `l` and empty output. -/
def cfgOf (l : List Bool) (v : Bool × Bool) : machine.Cfg :=
  ⟨some (), v, fun k => cond k [] l⟩

theorem step_cons (b : Bool) (l : List Bool) (v : Bool × Bool) :
    machine.step (cfgOf (b :: l) v) = some (cfgOf l (v.1 && b, true)) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem step_nil (v : Bool × Bool) :
    machine.step (cfgOf [] v) =
      some ⟨none, (true, false), fun k => cond k [v.1] []⟩ := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem run (l : List Bool) (v : Bool × Bool) :
    (flip bind machine.step)^[l.length + 1] (some (cfgOf l v)) =
      some ⟨none, (true, false), fun k => cond k [v.1 && decide (∀ c ∈ l, c = true)] []⟩ := by
  induction l generalizing v with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    show machine.step (cfgOf [] v) = _
    rw [step_nil v]
    simp
  | cons b l ih =>
    rw [List.length_cons, Nat.add_succ, Function.iterate_succ_apply]
    rw [show (flip bind machine.step) (some (cfgOf (b :: l) v)) =
        some (cfgOf l (v.1 && b, true)) from step_cons b l v]
    rw [ih (v.1 && b, true)]
    have e : ((v.1 && b) && decide (∀ c ∈ l, c = true)) =
        (v.1 && decide (∀ c ∈ b :: l, c = true)) := by
      cases b <;> cases v.1 <;> simp [List.forall_mem_cons]
    dsimp only
    rw [e]

theorem init_eq (a : List Bool) :
    initList machine a = cfgOf a (true, false) := by
  simp [initList, cfgOf, machine]
  congr 1
  funext k
  cases k <;> simp

theorem halt_eq (b : Bool) :
    haltList machine [b] = ⟨none, (true, false), fun k => cond k [b] []⟩ := by
  simp [haltList, machine]
  congr 1
  funext k
  cases k <;> simp

theorem main : InP (fun y : List Bool => decide (∀ b ∈ y, b = true)) := by
  refine ⟨{ tm := machine
            inputAlphabet := Equiv.refl Bool
            outputAlphabet := Equiv.refl Bool
            time := Polynomial.X + 1
            outputsFun := fun a => ?_ }⟩
  refine ⟨⟨a.length + 1, ?_⟩, ?_⟩
  · show (flip bind machine.step)^[a.length + 1]
        (some (initList machine (List.map (Equiv.refl Bool).invFun (id a)))) =
      Option.map (haltList machine)
        (some (List.map (Equiv.refl Bool).invFun
          (encodeBool (decide (∀ b ∈ a, b = true)))))
    have h : List.map (Equiv.refl Bool).invFun (id a) = a := by simp
    have h2 : List.map (Equiv.refl Bool).invFun (encodeBool (decide (∀ b ∈ a, b = true))) =
        [decide (∀ b ∈ a, b = true)] := by
      simp [encodeBool]
    simp only [h, h2]
    rw [init_eq, run, Option.map_some, halt_eq]
    simp
  · simp

end MPP.Solutions.Pnp122
