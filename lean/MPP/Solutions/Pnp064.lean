import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp064

open Computability Turing Turing.TM2.Stmt

/-- One input stack and one output stack. Label `true` skips the first input symbol. Label `false`
copies the rest: it pops a symbol, and if there was one it pushes `false` onto the output and loops;
otherwise it halls with the state `false`, which is the initial state. -/
abbrev machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Bool
  main := true
  σ := Bool
  initialState := false
  m
    | true => pop false (fun _ _ => false) (goto fun _ => false)
    | false => pop false (fun _ o => o.isSome)
        (branch (fun v => v) (push true (fun _ => false) (goto fun _ => false)) halt)

/-- Configuration with label `lab`, state `v`, input `l` and output `out`. -/
def cfgOf (l out : List Bool) (lab v : Bool) : machine.Cfg :=
  ⟨some lab, v, fun k => cond k out l⟩

theorem skip_step (b : Bool) (l out : List Bool) (v : Bool) :
    machine.step (cfgOf (b :: l) out true v) = some (cfgOf l out false false) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem skip_step_nil (out : List Bool) (v : Bool) :
    machine.step (cfgOf [] out true v) = some (cfgOf [] out false false) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem copy_step_cons (b : Bool) (l out : List Bool) (v : Bool) :
    machine.step (cfgOf (b :: l) out false v) = some (cfgOf l (false :: out) false true) := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem copy_step_nil (out : List Bool) (v : Bool) :
    machine.step (cfgOf [] out false v) =
      some ⟨none, false, fun k => cond k out []⟩ := by
  simp [FinTM2.step, cfgOf, machine, TM2.step, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp

theorem run (l out : List Bool) (v : Bool) :
    (flip bind machine.step)^[l.length + 1] (some (cfgOf l out false v)) =
      some ⟨none, false, fun k => cond k (List.replicate l.length false ++ out) []⟩ := by
  induction l generalizing out v with
  | nil =>
    rw [List.length_nil, zero_add, Function.iterate_one]
    show machine.step (cfgOf [] out false v) = _
    rw [copy_step_nil]
    simp
  | cons b l ih =>
    rw [List.length_cons, Nat.add_succ, Function.iterate_succ_apply]
    rw [show (flip bind machine.step) (some (cfgOf (b :: l) out false v)) =
        some (cfgOf l (false :: out) false true) from copy_step_cons b l out v]
    rw [ih (false :: out) true]
    simp [List.replicate_succ', List.append_assoc]

theorem init_eq (a : List Bool) : initList machine a = cfgOf a [] true false := by
  simp [initList, cfgOf, machine]
  congr 1
  funext k
  cases k <;> simp

theorem halt_eq (out : List Bool) :
    haltList machine out = ⟨none, false, fun k => cond k out []⟩ := by
  simp [haltList, machine]
  congr 1
  funext k
  cases k <;> simp

theorem main : ∃ D : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) D) ∧
    ∀ n : ℕ, D (List.replicate (n + 1) false) = List.replicate n false := by
  refine ⟨fun a => List.replicate (a.length - 1) false,
    ⟨{ tm := machine
       inputAlphabet := Equiv.refl Bool
       outputAlphabet := Equiv.refl Bool
       time := Polynomial.X + 2
       outputsFun := fun a => ?_ }⟩, fun n => by simp⟩
  cases a with
  | nil =>
    refine ⟨⟨2, ?_⟩, ?_⟩
    · have h : List.map (Equiv.refl Bool).invFun (id ([] : List Bool)) = [] := by simp
      simp only [h, List.length_nil, Nat.zero_sub, List.replicate_zero, List.map_nil]
      rw [init_eq, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply]
      rw [show (flip bind machine.step) (some (cfgOf [] [] true false)) =
          some (cfgOf [] [] false false) from skip_step_nil [] false]
      rw [Function.iterate_one, show (flip bind machine.step) (some (cfgOf [] [] false false)) =
          some ⟨none, false, fun k => cond k [] []⟩ from copy_step_nil [] false]
      rw [Option.map_some, halt_eq]
    · simp
  | cons b l =>
    refine ⟨⟨l.length + 2, ?_⟩, ?_⟩
    · have h : List.map (Equiv.refl Bool).invFun (id (b :: l)) = b :: l := by simp
      have h2 : List.map (Equiv.refl Bool).invFun
          (id (List.replicate ((b :: l).length - 1) false)) = List.replicate l.length false := by
        simp
      simp only [h, h2]
      rw [init_eq, show l.length + 2 = (l.length + 1) + 1 from rfl, Function.iterate_succ_apply]
      rw [show (flip bind machine.step) (some (cfgOf (b :: l) [] true false)) =
          some (cfgOf l [] false false) from skip_step b l [] false]
      rw [run, Option.map_some, halt_eq]
      simp
    · simp

end MPP.Solutions.Pnp064
