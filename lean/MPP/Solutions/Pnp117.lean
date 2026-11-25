import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp117

open Turing

/-- Program of the drop-one map. Label 0 pops the first symbol of the input and moves on, whatever it
is (on an empty input the popped value is `none`). Label 1 pops the rest of the input onto the
accumulator (stack 2), which reverses it. Label 2 pops the accumulator onto the output (stack 1),
which reverses it back, and halts when the accumulator is empty. -/
def prog : Fin 3 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)
  | 0 => .pop 0 (fun _ h => h) (.goto fun _ => 1)
  | 1 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 2 (fun s => s.getD false) (.goto fun _ => 1))
        (.goto fun _ => 2))
  | 2 => .pop 2 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.goto fun _ => 2))
        (.load (fun _ => none) .halt))

/-- The drop-one map as a finite machine: stacks `0` (input), `1` (output), `2` (accumulator). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m := prog

/-- Configuration with label `l`, state `v`, input stack `R`, output stack `O`, accumulator `B`. -/
def cfg (l : Fin 3) (v : Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  ⟨some l, v, ![R, O, B]⟩

theorem step0_cons (v : Option Bool) (a : Bool) (R O B : List Bool) :
    TM2.step prog (cfg 0 v (a :: R) O B) = some (cfg 1 (some a) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 0 v [] O B) = some (cfg 1 none [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_push (a : Bool) (v : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 1 v (a :: R) O B) = some (cfg 1 (some a) R O (a :: B)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_end (v : Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 1 v [] O B) = some (cfg 2 none [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_push (a : Bool) (v : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 2 v R O (a :: B)) = some (cfg 2 (some a) R (a :: O) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_end (v : Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 2 v R O []) = some ⟨none, none, ![R, O, []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Label 0 pops one symbol in a single step, leaving the rest on the input. -/
theorem phase0 : ∀ (w : List Bool) (v : Option Bool) (O B : List Bool),
    rn 1 (cfg 0 v w O B) = some (cfg 1 w.head? w.tail O B)
  | [], v, O, B => by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_nil v O B)]
      simp [rn]
  | a :: R, v, O, B => by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_cons v a R O B)]
      simp [rn]

/-- Label 1 moves the rest of the input onto the accumulator, which reverses it. -/
theorem phase1 : ∀ (R B O : List Bool) (v : Option Bool),
    rn (R.length + 1) (cfg 1 v R O B) = some (cfg 2 none [] O (R.reverse ++ B))
  | [], B, O, v => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step1_end v O B)]
      simp [rn]
  | a :: R, B, O, v => by
      rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl,
        rn_succ_step (step1_push a v R O B)]
      rw [phase1 R (a :: B) O (some a)]
      simp [List.reverse_cons, List.append_assoc]

/-- Label 2 moves the accumulator onto the output, which reverses it back. -/
theorem phase2 : ∀ (B O : List Bool) (v : Option Bool),
    rn (B.length + 1) (cfg 2 v [] O B) = some ⟨none, none, ![[], B.reverse ++ O, []]⟩
  | [], O, v => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step2_end v [] O)]
      simp [rn]
  | a :: B, O, v => by
      rw [show (a :: B).length + 1 = (B.length + 1) + 1 from rfl,
        rn_succ_step (step2_push a v [] O B)]
      rw [phase2 B (a :: O) (some a)]
      simp [List.reverse_cons, List.append_assoc]

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

/-- Every input is dropped to its tail by the machine in at most `2|w| + 3` steps. -/
theorem gen (w : List Bool) : ∃ s, s ≤ 2 * w.length + 3 ∧
    rn s (cfg 0 none w [] []) = some ⟨none, none, ![[], w.tail, []]⟩ := by
  have hlen0 : w.tail.length ≤ w.length := by
    rw [List.length_tail]
    omega
  have h0 := phase0 w none [] []
  generalize hR : w.tail = R at h0 hlen0 ⊢
  have h1 : rn (R.length + 1) (cfg 1 w.head? R [] []) = some (cfg 2 none [] [] R.reverse) := by
    have := phase1 R [] [] w.head?
    simpa using this
  have h2 : rn (R.reverse.length + 1) (cfg 2 none [] [] R.reverse) =
      some ⟨none, none, ![[], R, []]⟩ := by
    have := phase2 R.reverse [] none
    simpa using this
  have hA : rn (R.length + 1 + 1) (cfg 0 none w [] []) = some (cfg 2 none [] [] R.reverse) := by
    rw [rn_add (n := R.length + 1) h0]
    exact h1
  have hB : rn (R.reverse.length + 1 + (R.length + 1 + 1)) (cfg 0 none w [] []) =
      some ⟨none, none, ![[], R, []]⟩ := by
    rw [rn_add hA]
    exact h2
  refine ⟨R.reverse.length + 1 + (R.length + 1 + 1), ?_, hB⟩
  simp only [List.length_reverse]
  omega

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) List.tail where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun z := by
    have hs := (gen z).choose_spec.1
    have he := (gen z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(gen z).choose] (some (initList tm z)) =
        some (haltList tm z.tail) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id z.tail)
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ x : List Bool, T x = x.tail :=
  ⟨List.tail, ⟨machine⟩, fun _ => rfl⟩

end MPP.Solutions.Pnp117
