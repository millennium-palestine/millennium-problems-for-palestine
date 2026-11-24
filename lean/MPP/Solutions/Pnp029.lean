import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp029

open Turing

/-- Program of the unary-length machine. The single label 0 pops one symbol of the input stack
(stack 0). If there was one, it pushes `false` onto the output stack (stack 1) and repeats; if the
input is empty it halts. One loop iteration is one machine step. -/
def prog : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun _ => false) (.goto fun _ => 0))
        .halt)

/-- The unary-length machine: stacks `0` (input) and `1` (output). -/
def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 1
  main := 0
  σ := Option Bool
  initialState := none
  m := prog

/-- Configuration with the loop label, state `v`, input stack `R` and output stack `O`. -/
def cfg (v : Option Bool) (R O : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool) :=
  ⟨some 0, v, ![R, O]⟩

theorem step_cons (a : Bool) (v : Option Bool) (R O : List Bool) :
    TM2.step prog (cfg v (a :: R) O) = some (cfg (some a) R (false :: O)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step_nil (v : Option Bool) (O : List Bool) :
    TM2.step prog (cfg v [] O) = some ⟨none, none, ![[], O]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem run (x O : List Bool) (v : Option Bool) :
    rn (x.length + 1) (cfg v x O) = some ⟨none, none, ![[], List.replicate x.length false ++ O]⟩ := by
  induction x generalizing O v with
  | nil =>
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step_nil v O)]
    simp [rn]
  | cons a x ih =>
    rw [show (a :: x).length + 1 = (x.length + 1) + 1 from rfl,
      rn_succ_step (step_cons a v x O), ih (false :: O) (some a)]
    simp [List.replicate_succ', List.append_assoc]

/-- The unary length of the input, as a function. -/
def g (x : List Bool) : List Bool := List.replicate x.length false

theorem initList_eq (z : List Bool) : initList tm z = cfg none z [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) : haltList tm O = ⟨none, none, ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun x := by
    have key : (fun o => o.bind (TM2.step prog))^[x.length + 1] (some (initList tm x)) =
        some (haltList tm (g x)) := by
      rw [initList_eq, haltList_eq]
      have h := run x [] none
      rw [List.append_nil] at h
      exact h
    refine ⟨⟨x.length + 1, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id x)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (g x))
    · simp

theorem main : ∃ g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) ∧
    ∀ x : List Bool, g x = List.replicate x.length false :=
  ⟨g, ⟨machine⟩, fun _ => rfl⟩

end MPP.Solutions.Pnp029
