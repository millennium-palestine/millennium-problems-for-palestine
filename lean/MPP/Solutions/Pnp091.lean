import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp091

open Computability Turing MPP.PvsNP

/-- The state: the last symbol popped from the input (`none` once the input is empty), and the
parity of the ones read so far (`true` when odd). -/
abbrev St := Option Bool × Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) St

/-- Program of the parity machine. Stacks: `0` input, `1` output. Label 0 pops the input; a symbol
flips the parity and the loop repeats; an empty input goes to label 1. Label 1 pushes the negated
parity onto the output and halts, with the state reset to the initial one. -/
def prog : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) St
  | 0 => .pop 0 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.load (fun s => (none, xor s.2 (s.1.getD false))) (.goto fun _ => 0))
        (.goto fun _ => 1))
  | 1 => .push 1 (fun s => !s.2) (.load (fun _ => (none, false)) .halt)

/-- The parity machine: input stack `0`, output stack `1`. -/
def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 2
  main := 0
  σ := St
  initialState := (none, false)
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input) and `O` (output). -/
def cfg (l : Fin 2) (v : St) (R O : List Bool) : Cfg :=
  ⟨some l, v, ![R, O]⟩

theorem step0_cons (a : Bool) (v : St) (R O : List Bool) :
    TM2.step prog (cfg 0 v (a :: R) O) = some (cfg 0 (none, xor v.2 a) R O) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : St) (O : List Bool) :
    TM2.step prog (cfg 0 v [] O) = some (cfg 1 (none, v.2) [] O) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_halt (v : St) (O : List Bool) :
    TM2.step prog (cfg 1 v [] O) = some ⟨none, (none, false), ![[], (!v.2) :: O]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

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

/-- Adding one symbol `a` to the front of `R` flips the parity exactly when `a` is `true`. -/
theorem par_step (p a : Bool) (R : List Bool) :
    xor (xor p a) (decide (R.count true % 2 = 1)) = xor p (decide ((a :: R).count true % 2 = 1)) := by
  cases a <;> cases p <;> rcases Nat.mod_two_eq_zero_or_one (R.count true) with h | h <;>
    simp [List.count_cons, h, Nat.add_mod]

/-- Phase 0: the input is read symbol by symbol, and the parity of its ones is kept in the state. -/
theorem copy : ∀ (R O : List Bool) (v : St),
    rn (R.length + 1) (cfg 0 v R O) = some (cfg 1 (none, xor v.2 (decide (R.count true % 2 = 1))) [] O)
  | [], O, v => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step0_nil v O)]
    simp [rn]
  | a :: R, O, v => by
    rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl, rn_succ_step (step0_cons a v R O)]
    rw [copy R O (none, xor v.2 a)]
    dsimp only
    rw [par_step]

theorem not_decide_odd (n : ℕ) : (!decide (n % 2 = 1)) = decide (n % 2 = 0) := by
  by_cases h : n % 2 = 1 <;> simp [h] <;> omega

/-- The whole run on an input `z`: phase 0 followed by the halting step, in `|z| + 2` steps. -/
theorem run (z : List Bool) : rn (1 + (z.length + 1)) (cfg 0 (none, false) z []) =
    some ⟨none, (none, false), ![[], [decide (z.count true % 2 = 0)]]⟩ := by
  rw [rn_add (copy z [] (none, false))]
  show rn (0 + 1) _ = _
  rw [rn_succ_step (step1_halt _ [])]
  simp [rn, not_decide_odd]

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, false) z [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, (none, false), ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool
      (fun x : List Bool => decide (x.count true % 2 = 0)) where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[1 + (z.length + 1)] (some (initList tm z)) =
        some (haltList tm [decide (z.count true % 2 = 0)]) := by
      rw [initList_eq, haltList_eq]
      exact run z
    refine ⟨⟨1 + (z.length + 1), ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

theorem main : InP (fun x : List Bool => decide (x.count true % 2 = 0)) :=
  ⟨machine⟩

end MPP.Solutions.Pnp091
