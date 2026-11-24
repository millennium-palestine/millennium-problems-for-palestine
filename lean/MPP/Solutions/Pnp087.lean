import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp087

open Computability Turing MPP.PvsNP

/-- The state: the last symbol popped from the input, or `none` once the input is empty. -/
abbrev St := Option Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) St

/-- Program of the reversal machine. Stacks: `0` input, `1` output. Label 0 pops the input; a
symbol is pushed onto the output and the loop repeats; an empty input goes to label 1, which halts.
Each symbol pushed onto the output ends up below the earlier ones, so the output is the reverse. -/
def prog : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) St
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.goto fun _ => 0))
        (.goto fun _ => 1))
  | 1 => .load (fun _ => none) .halt

/-- The reversal machine: input stack `0`, output stack `1`. -/
def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 2
  main := 0
  σ := St
  initialState := none
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input) and `O` (output). -/
def cfg (l : Fin 2) (v : St) (R O : List Bool) : Cfg :=
  ⟨some l, v, ![R, O]⟩

theorem step0_push (a : Bool) (v : St) (R O : List Bool) :
    TM2.step prog (cfg 0 v (a :: R) O) = some (cfg 0 (some a) R (a :: O)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]
  funext k
  fin_cases k <;> simp

theorem step0_end (v : St) (O : List Bool) :
    TM2.step prog (cfg 0 v [] O) = some (cfg 1 none [] O) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

theorem step1_halt (v : St) (O : List Bool) :
    TM2.step prog (cfg 1 v [] O) = some ⟨none, none, ![[], O]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : Cfg) : Option Cfg :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ} {c c' : Cfg} (h : TM2.step prog c = some c') :
    rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ} {c c' : Cfg} (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Phase 0: the input is popped symbol by symbol and each symbol is pushed onto the output. -/
theorem copy (R O : List Bool) (v : St) :
    rn (R.length + 1) (cfg 0 v R O) = some (cfg 1 none [] (R.reverse ++ O)) := by
  induction R generalizing O v with
  | nil =>
    rw [rn_succ_step (step0_end v O)]
    simp [rn]
  | cons a R ih =>
    rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl, rn_succ_step (step0_push a v R O)]
    rw [ih (a :: O) (some a)]
    simp [cfg, List.reverse_cons, List.append_assoc]

/-- The whole run on an input `z`: phase 0 followed by the halting step. -/
theorem run (z : List Bool) : ∃ s, s ≤ z.length + 2 ∧
    rn s (cfg 0 none z []) = some ⟨none, none, ![[], z.reverse]⟩ := by
  have h1 := copy z [] none
  rw [List.append_nil] at h1
  refine ⟨1 + (z.length + 1), by omega, ?_⟩
  rw [rn_add h1]
  show rn (0 + 1) (cfg 1 none [] z.reverse) = _
  rw [rn_succ_step (step1_halt none z.reverse)]
  simp [rn]

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 none z [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, none, ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (List.reverse : List Bool → List Bool) where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[(run z).choose] (some (initList tm z)) =
        some (haltList tm z.reverse) := by
      rw [initList_eq, haltList_eq]
      exact (run z).choose_spec.2
    refine ⟨⟨(run z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id z.reverse)
    · have := (run z).choose_spec.1
      simp only [id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

theorem main : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
    (List.reverse : List Bool → List Bool)) :=
  ⟨machine⟩

end MPP.Solutions.Pnp087
