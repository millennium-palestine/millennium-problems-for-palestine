import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp088

open Computability Turing MPP.PvsNP

/-- The state: the last symbol popped from the stack being emptied, or `none` once it is empty. -/
abbrev St := Option Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) St

/-- Program of the doubling machine. Stacks: `0` input, `1` output, `2` temporary.
Label 0 moves the input onto stack `2`, which then holds the input reversed. Label 1 moves stack `2`
onto stack `1` and also onto stack `0`: stack `1` then holds the input, and stack `0` holds it
too, with the order restored. Label 2 moves stack `0` onto stack `2`, reversing it again. Label 3
moves stack `2` onto stack `1`, which appends the input after the first copy. Label 4 halts. -/
def prog : Fin 5 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) St
  | 0 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 2 (fun s => s.getD false) (.goto fun _ => 0))
        (.goto fun _ => 1))
  | 1 => .pop 2 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.push 0 (fun s => s.getD false) (.goto fun _ => 1)))
        (.goto fun _ => 2))
  | 2 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 2 (fun s => s.getD false) (.goto fun _ => 2))
        (.goto fun _ => 3))
  | 3 => .pop 2 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.goto fun _ => 3))
        (.goto fun _ => 4))
  | 4 => .load (fun _ => none) .halt

/-- The doubling machine: stacks `0` input, `1` output, `2` temporary. -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 5
  main := 0
  σ := St
  initialState := none
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `I` (input), `O` (output), `T` (temporary). -/
def cfg (l : Fin 5) (v : St) (I O T : List Bool) : Cfg :=
  ⟨some l, v, ![I, O, T]⟩

theorem step0_push (a : Bool) (v : St) (I O T : List Bool) :
    TM2.step prog (cfg 0 v (a :: I) O T) = some (cfg 0 (some a) I O (a :: T)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]
  funext k
  fin_cases k <;> simp

theorem step0_end (v : St) (O T : List Bool) :
    TM2.step prog (cfg 0 v [] O T) = some (cfg 1 none [] O T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

theorem step1_push (a : Bool) (v : St) (I O T : List Bool) :
    TM2.step prog (cfg 1 v I O (a :: T)) = some (cfg 1 (some a) (a :: I) (a :: O) T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]
  funext k
  fin_cases k <;> simp

theorem step1_end (v : St) (I O : List Bool) :
    TM2.step prog (cfg 1 v I O []) = some (cfg 2 none I O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

theorem step2_push (a : Bool) (v : St) (I O T : List Bool) :
    TM2.step prog (cfg 2 v (a :: I) O T) = some (cfg 2 (some a) I O (a :: T)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]
  funext k
  fin_cases k <;> simp

theorem step2_end (v : St) (O T : List Bool) :
    TM2.step prog (cfg 2 v [] O T) = some (cfg 3 none [] O T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

theorem step3_push (a : Bool) (v : St) (I O T : List Bool) :
    TM2.step prog (cfg 3 v I O (a :: T)) = some (cfg 3 (some a) I (a :: O) T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]
  funext k
  fin_cases k <;> simp

theorem step3_end (v : St) (I O : List Bool) :
    TM2.step prog (cfg 3 v I O []) = some (cfg 4 none I O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg]

theorem step4 (v : St) (I O T : List Bool) :
    TM2.step prog (cfg 4 v I O T) = some ⟨none, none, ![I, O, T]⟩ := by
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

/-- Label 0: the input is moved onto stack `2`, so stack `2` holds the input reversed. -/
theorem phaseA (I O T : List Bool) (v : St) :
    rn (I.length + 1) (cfg 0 v I O T) = some (cfg 1 none [] O (I.reverse ++ T)) := by
  induction I generalizing T v with
  | nil =>
    rw [rn_succ_step (step0_end v O T)]
    simp [rn]
  | cons a I ih =>
    rw [show (a :: I).length + 1 = (I.length + 1) + 1 from rfl, rn_succ_step (step0_push a v I O T)]
    rw [ih (a :: T) (some a)]
    simp [cfg, List.reverse_cons, List.append_assoc]

/-- Label 1: stack `2` is moved onto stacks `1` and `0`, each getting the reversed order. -/
theorem phaseB (T I O : List Bool) (v : St) :
    rn (T.length + 1) (cfg 1 v I O T) = some (cfg 2 none (T.reverse ++ I) (T.reverse ++ O) []) := by
  induction T generalizing I O v with
  | nil =>
    rw [rn_succ_step (step1_end v I O)]
    simp [rn]
  | cons a T ih =>
    rw [show (a :: T).length + 1 = (T.length + 1) + 1 from rfl, rn_succ_step (step1_push a v I O T)]
    rw [ih (a :: I) (a :: O) (some a)]
    simp [cfg, List.reverse_cons, List.append_assoc]

/-- Label 2: stack `0` is moved onto stack `2`, so stack `2` holds the input in its original order
reversed once more. -/
theorem phaseC (I O T : List Bool) (v : St) :
    rn (I.length + 1) (cfg 2 v I O T) = some (cfg 3 none [] O (I.reverse ++ T)) := by
  induction I generalizing T v with
  | nil =>
    rw [rn_succ_step (step2_end v O T)]
    simp [rn]
  | cons a I ih =>
    rw [show (a :: I).length + 1 = (I.length + 1) + 1 from rfl, rn_succ_step (step2_push a v I O T)]
    rw [ih (a :: T) (some a)]
    simp [cfg, List.reverse_cons, List.append_assoc]

/-- Label 3: stack `2` is moved onto stack `1`, appending the input after the first copy. -/
theorem phaseD (T I O : List Bool) (v : St) :
    rn (T.length + 1) (cfg 3 v I O T) = some (cfg 4 none I (T.reverse ++ O) []) := by
  induction T generalizing I O v with
  | nil =>
    rw [rn_succ_step (step3_end v I O)]
    simp [rn]
  | cons a T ih =>
    rw [show (a :: T).length + 1 = (T.length + 1) + 1 from rfl, rn_succ_step (step3_push a v I O T)]
    rw [ih I (a :: O) (some a)]
    simp [cfg, List.reverse_cons, List.append_assoc]

theorem halt4 (O : List Bool) : rn 1 (cfg 4 none [] O []) = some ⟨none, none, ![[], O, []]⟩ := by
  show rn (0 + 1) (cfg 4 none [] O []) = _
  rw [rn_succ_step (step4 none [] O [])]
  simp [rn]

/-- The whole run on an input `z`: four phases of `|z| + 1` steps each, then the halting step. -/
theorem run (z : List Bool) : ∃ s, s ≤ 4 * z.length + 5 ∧
    rn s (cfg 0 none z [] []) = some ⟨none, none, ![[], z ++ z, []]⟩ := by
  have hA := phaseA z [] [] none
  rw [List.append_nil] at hA
  have hB := phaseB z.reverse [] [] none
  rw [List.length_reverse, List.reverse_reverse, List.append_nil] at hB
  have hC := phaseC z z [] none
  rw [List.append_nil] at hC
  have hD := phaseD z.reverse [] z none
  rw [List.length_reverse, List.reverse_reverse] at hD
  have hAB := (rn_add (n := z.length + 1) hA).trans hB
  have hABC := (rn_add (n := z.length + 1) hAB).trans hC
  have hABCD := (rn_add (n := z.length + 1) hABC).trans hD
  have hH := (rn_add (n := 1) hABCD).trans (halt4 (z ++ z))
  exact ⟨_, by omega, hH⟩

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 none z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, none, ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      (fun x : List Bool => x ++ x : List Bool → List Bool) where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 5
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[(run z).choose] (some (initList tm z)) =
        some (haltList tm (z ++ z)) := by
      rw [initList_eq, haltList_eq]
      exact (run z).choose_spec.2
    refine ⟨⟨(run z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (z ++ z))
    · have := (run z).choose_spec.1
      simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
    (fun x : List Bool => x ++ x : List Bool → List Bool)) :=
  ⟨machine⟩

end MPP.Solutions.Pnp088
