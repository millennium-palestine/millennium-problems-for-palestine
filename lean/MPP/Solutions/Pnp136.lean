import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp136

open MPP.PvsNP Turing

/-- Reads the first component of a string viewed as a doubled prefix followed by a separator.
Doubled pairs `a a` contribute `a` to the first component; the first pair that is not doubled
ends it, and the rest of the string is the second component. -/
def splitPair : List Bool → List Bool × List Bool
  | a :: b :: rest => if a = b then (a :: (splitPair rest).1, (splitPair rest).2) else ([], rest)
  | _ => ([], [])

theorem splitPair_eq (a : Bool) (rest : List Bool) :
    splitPair (a :: a :: rest) = (a :: (splitPair rest).1, (splitPair rest).2) := by
  simp [splitPair]

theorem splitPair_ne (a b : Bool) (h : a ≠ b) (rest : List Bool) :
    splitPair (a :: b :: rest) = ([], rest) := by
  simp [splitPair, h]

theorem splitPair_len : ∀ z : List Bool,
    (splitPair z).1.length + (splitPair z).2.length ≤ z.length
  | [] => by simp [splitPair]
  | [a] => by simp [splitPair]
  | a :: b :: rest => by
      by_cases h : a = b
      · subst h
        have := splitPair_len rest
        rw [splitPair_eq]
        simp only [List.length_cons]
        omega
      · rw [splitPair_ne a b h]
        simp only [List.length_nil, List.length_cons]
        omega

theorem splitPair_pair (x u : List Bool) : splitPair (pair x u) = (x, u) := by
  induction x with
  | nil => simp [pair, splitPair]
  | cons a x ih =>
      have e : pair (a :: x) u = a :: a :: pair x u := by simp [pair]
      rw [e, splitPair_eq, ih]

/-- Two-symbol test of label 1: keeps the bit when both popped symbols are equal. -/
def dbl : Option Bool → Option Bool → Option Bool
  | some a, some b => if a = b then some a else none
  | _, _ => none

/-- Program of the take map. Stack 0 is the input, stack 1 the output, stack 2 an accumulator,
stack 3 the taken prefix in reverse. Labels 0 to 2 are as in pnp-120: the doubled bits of the
first component go to stack 2 in reverse, and then to stack 1 in order. Label 3 pops one symbol
of the second component and one symbol of stack 1 for each step, and pushes the stack 1 symbol
onto stack 3; it stops when either is empty. Label 4 empties stack 1, label 5 empties stack 0,
label 6 moves stack 3 back onto stack 1, and label 7 halts. -/
def prog : Fin 8 → TM2.Stmt (fun _ : Fin 4 => Bool) (Fin 8) (Option Bool)
  | 0 => .pop 0 (fun _ h => h) (.goto fun _ => 1)
  | 1 => .pop 0 (fun s h => dbl s h)
      (.branch (fun s => s.isSome)
        (.push 2 (fun s => s.getD false) (.goto fun _ => 0))
        (.goto fun _ => 2))
  | 2 => .pop 2 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.goto fun _ => 2))
        (.goto fun _ => 3))
  | 3 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.pop 1 (fun _ h => h)
          (.branch (fun s => s.isSome)
            (.push 3 (fun s => s.getD false) (.goto fun _ => 3))
            (.goto fun _ => 4)))
        (.goto fun _ => 4))
  | 4 => .pop 1 (fun _ h => h)
      (.branch (fun s => s.isSome) (.goto fun _ => 4) (.goto fun _ => 5))
  | 5 => .pop 0 (fun _ h => h)
      (.branch (fun s => s.isSome) (.goto fun _ => 5) (.goto fun _ => 6))
  | 6 => .pop 3 (fun _ h => h)
      (.branch (fun s => s.isSome)
        (.push 1 (fun s => s.getD false) (.goto fun _ => 6))
        (.goto fun _ => 7))
  | 7 => .load (fun _ => none) .halt

/-- The take map as a finite machine: stacks `0` (input), `1` (output), `2` (accumulator),
`3` (taken prefix). -/
def tm : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 8
  main := 0
  σ := Option Bool
  initialState := none
  m := prog

/-- Configuration with label `l`, state `v`, stacks `R` (0), `O` (1), `B` (2), `C` (3). -/
def cfg (l : Fin 8) (v : Option Bool) (R O B C : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 8) (Option Bool) :=
  ⟨some l, v, ![R, O, B, C]⟩

abbrev Cf := TM2.Cfg (fun _ : Fin 4 => Bool) (Fin 8) (Option Bool)

theorem s0_cons (v : Option Bool) (a : Bool) (R O B C : List Bool) :
    TM2.step prog (cfg 0 v (a :: R) O B C) = some (cfg 1 (some a) R O B C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s0_nil (v : Option Bool) (O B C : List Bool) :
    TM2.step prog (cfg 0 v [] O B C) = some (cfg 1 none [] O B C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s1_eq (a : Bool) (R O B C : List Bool) :
    TM2.step prog (cfg 1 (some a) (a :: R) O B C) = some (cfg 0 (some a) R O (a :: B) C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg, dbl] <;> (funext j; fin_cases j <;> simp)

theorem s1_ne (a b : Bool) (h : a ≠ b) (R O B C : List Bool) :
    TM2.step prog (cfg 1 (some a) (b :: R) O B C) = some (cfg 2 none R O B C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg, dbl, h] <;> (funext j; fin_cases j <;> simp)

theorem s1_nil (v : Option Bool) (O B C : List Bool) :
    TM2.step prog (cfg 1 v [] O B C) = some (cfg 2 none [] O B C) := by
  cases v <;> simp [TM2.step, TM2.stepAux, prog, cfg, dbl] <;> (funext j; fin_cases j <;> simp)

theorem s2_cons (a : Bool) (v : Option Bool) (R O B C : List Bool) :
    TM2.step prog (cfg 2 v R O (a :: B) C) = some (cfg 2 (some a) R (a :: O) B C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s2_nil (v : Option Bool) (R O C : List Bool) :
    TM2.step prog (cfg 2 v R O [] C) = some (cfg 3 none R O [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

/-- Label 3, one symbol of the second component and one symbol of the output both present. -/
theorem s3_cons (v : Option Bool) (a c : Bool) (u O C : List Bool) :
    TM2.step prog (cfg 3 v (a :: u) (c :: O) [] C) = some (cfg 3 (some c) u O [] (c :: C)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

/-- Label 3, the output is empty: one symbol of the second component is consumed, then stop. -/
theorem s3_nilO (v : Option Bool) (a : Bool) (u C : List Bool) :
    TM2.step prog (cfg 3 v (a :: u) [] [] C) = some (cfg 4 none u [] [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

/-- Label 3, the second component is empty: stop. -/
theorem s3_nilU (v : Option Bool) (O C : List Bool) :
    TM2.step prog (cfg 3 v [] O [] C) = some (cfg 4 none [] O [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s4_cons (v : Option Bool) (c : Bool) (R O C : List Bool) :
    TM2.step prog (cfg 4 v R (c :: O) [] C) = some (cfg 4 (some c) R O [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s4_nil (v : Option Bool) (R C : List Bool) :
    TM2.step prog (cfg 4 v R [] [] C) = some (cfg 5 none R [] [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s5_cons (v : Option Bool) (a : Bool) (R C : List Bool) :
    TM2.step prog (cfg 5 v (a :: R) [] [] C) = some (cfg 5 (some a) R [] [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s5_nil (v : Option Bool) (C : List Bool) :
    TM2.step prog (cfg 5 v [] [] [] C) = some (cfg 6 none [] [] [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s6_cons (v : Option Bool) (c : Bool) (O C : List Bool) :
    TM2.step prog (cfg 6 v [] O [] (c :: C)) = some (cfg 6 (some c) [] (c :: O) [] C) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s6_nil (v : Option Bool) (O : List Bool) :
    TM2.step prog (cfg 6 v [] O [] []) = some (cfg 7 none [] O [] []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s7_halt (v : Option Bool) (O : List Bool) :
    TM2.step prog (cfg 7 v [] O [] []) = some ⟨none, none, ![[], O, [], []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : Cf) : Option Cf :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ} {c c' : Cf} (h : TM2.step prog c = some c') :
    rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_zero (c : Cf) : rn 0 c = some c := rfl

theorem rn_add {m n : ℕ} {c c' : Cf} (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem rn_trans {m n : ℕ} {c c' c'' : Cf} (h1 : rn m c = some c') (h2 : rn n c' = some c'') :
    rn (n + m) c = some c'' := by
  rw [rn_add h1]
  exact h2

/-- Phase 1: the doubled pairs of the input are read; their bits go onto the accumulator in
reverse order, and the rest of the input after the first non-doubled pair is left on stack 0. -/
theorem phase1 : ∀ (z B : List Bool) (v : Option Bool),
    ∃ s, s ≤ z.length + 2 ∧
      rn s (cfg 0 v z [] B []) = some (cfg 2 none (splitPair z).2 [] ((splitPair z).1.reverse ++ B) [])
  | [], B, v => ⟨2, by simp, by
      show rn (0 + 1 + 1) (cfg 0 v [] [] B []) = _
      rw [rn_succ_step (s0_nil v [] B []), rn_succ_step (s1_nil none [] B [])]
      simp [rn, splitPair]⟩
  | [a], B, v => ⟨2, by simp, by
      show rn (0 + 1 + 1) (cfg 0 v [a] [] B []) = _
      rw [rn_succ_step (s0_cons v a [] [] B []), rn_succ_step (s1_nil (some a) [] B [])]
      simp [rn, splitPair]⟩
  | a :: b :: rest, B, v => by
      by_cases h : a = b
      · subst h
        obtain ⟨s, hs, hrun⟩ := phase1 rest (a :: B) (some a)
        refine ⟨s + 1 + 1, by simp only [List.length_cons]; omega, ?_⟩
        show rn (s + 1 + 1) (cfg 0 v (a :: a :: rest) [] B []) = _
        rw [rn_succ_step (s0_cons v a (a :: rest) [] B []), rn_succ_step (s1_eq a rest [] B []), hrun,
          splitPair_eq]
        simp [List.reverse_cons, List.append_assoc]
      · refine ⟨2, by simp, ?_⟩
        show rn (0 + 1 + 1) (cfg 0 v (a :: b :: rest) [] B []) = _
        rw [rn_succ_step (s0_cons v a (b :: rest) [] B []), rn_succ_step (s1_ne a b h rest [] B []),
          splitPair_ne a b h]
        simp [rn]

/-- Phase 2: the accumulator is moved onto the output, which reverses it. -/
theorem phase2 : ∀ (B O R C : List Bool) (v : Option Bool),
    rn (B.length + 1) (cfg 2 v R O B C) = some (cfg 3 none R (B.reverse ++ O) [] C)
  | [], O, R, C, v => by
      show rn (0 + 1) (cfg 2 v R O [] C) = _
      rw [rn_succ_step (s2_nil v R O C)]
      simp [rn]
  | a :: B, O, R, C, v => by
      show rn (B.length + 1 + 1) (cfg 2 v R O (a :: B) C) = _
      rw [rn_succ_step (s2_cons a v R O B C), phase2 B (a :: O) R C (some a)]
      simp [List.reverse_cons, List.append_assoc]

/-- Phase 3: the loop of label 3. Each step consumes one symbol of the second component, so it
takes at most `|u| + 1` steps. The taken prefix is pushed onto stack 3 in reverse order. -/
theorem phase3 : ∀ (u O C : List Bool) (v : Option Bool),
    ∃ s, s ≤ u.length + 1 ∧ ∃ R' O' : List Bool, R'.length ≤ u.length ∧ O'.length ≤ O.length ∧
      rn s (cfg 3 v u O [] C) = some (cfg 4 none R' O' [] ((O.take u.length).reverse ++ C))
  | [], O, C, v => ⟨1, by simp, [], O, by simp, by simp, by
      show rn (0 + 1) (cfg 3 v [] O [] C) = _
      rw [rn_succ_step (s3_nilU v O C)]
      simp [rn]⟩
  | a :: u, [], C, v => ⟨1, by simp, u, [], by simp, by simp, by
      show rn (0 + 1) (cfg 3 v (a :: u) [] [] C) = _
      rw [rn_succ_step (s3_nilO v a u C)]
      simp [rn]⟩
  | a :: u, c :: O, C, v => by
      obtain ⟨s, hs, R', O', hR, hO, hrun⟩ := phase3 u O (c :: C) (some c)
      refine ⟨s + 1, by simp only [List.length_cons]; omega, R', O', by simp; omega, by simp; omega, ?_⟩
      show rn (s + 1) (cfg 3 v (a :: u) (c :: O) [] C) = _
      rw [rn_succ_step (s3_cons v a c u O C), hrun]
      simp [List.take_succ_cons, List.reverse_cons, List.append_assoc]

/-- Phase 4: stack 1 is emptied. -/
theorem phase4 : ∀ (O R C : List Bool) (v : Option Bool),
    rn (O.length + 1) (cfg 4 v R O [] C) = some (cfg 5 none R [] [] C)
  | [], R, C, v => by
      show rn (0 + 1) (cfg 4 v R [] [] C) = _
      rw [rn_succ_step (s4_nil v R C)]
      simp [rn]
  | c :: O, R, C, v => by
      show rn (O.length + 1 + 1) (cfg 4 v R (c :: O) [] C) = _
      rw [rn_succ_step (s4_cons v c R O C), phase4 O R C (some c)]

/-- Phase 5: stack 0 is emptied. -/
theorem phase5 : ∀ (R C : List Bool) (v : Option Bool),
    rn (R.length + 1) (cfg 5 v R [] [] C) = some (cfg 6 none [] [] [] C)
  | [], C, v => by
      show rn (0 + 1) (cfg 5 v [] [] [] C) = _
      rw [rn_succ_step (s5_nil v C)]
      simp [rn]
  | a :: R, C, v => by
      show rn (R.length + 1 + 1) (cfg 5 v (a :: R) [] [] C) = _
      rw [rn_succ_step (s5_cons v a R C), phase5 R C (some a)]

/-- Phase 6: the taken prefix moves from stack 3 back to stack 1, which restores its order. -/
theorem phase6 : ∀ (C O : List Bool) (v : Option Bool),
    rn (C.length + 1) (cfg 6 v [] O [] C) = some (cfg 7 none [] (C.reverse ++ O) [] [])
  | [], O, v => by
      show rn (0 + 1) (cfg 6 v [] O [] []) = _
      rw [rn_succ_step (s6_nil v O)]
      simp [rn]
  | c :: C, O, v => by
      show rn (C.length + 1 + 1) (cfg 6 v [] O [] (c :: C)) = _
      rw [rn_succ_step (s6_cons v c O C), phase6 C (c :: O) (some c)]
      simp [List.reverse_cons, List.append_assoc]

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 none z [] [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (j : Fin 4) => ?_
  fin_cases j <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, none, ![[], O, [], []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (j : Fin 4) => ?_
  fin_cases j <;> simp [tm]

/-- The take map, defined on every input as the machine computes it. -/
def Tk (z : List Bool) : List Bool := (splitPair z).1.take (splitPair z).2.length

/-- Every input is mapped by the machine in at most `6|z| + 10` steps. -/
theorem gen (z : List Bool) : ∃ s, s ≤ 6 * z.length + 10 ∧
    rn s (cfg 0 none z [] [] []) = some ⟨none, none, ![[], Tk z, [], []]⟩ := by
  obtain ⟨s1, hs1, h1⟩ := phase1 z [] none
  rw [List.append_nil] at h1
  have h2 := phase2 (splitPair z).1.reverse [] (splitPair z).2 [] none
  rw [List.append_nil, List.reverse_reverse] at h2
  have hl := splitPair_len z
  obtain ⟨s3, hs3, R', O', hR, hO, h3⟩ := phase3 (splitPair z).2 (splitPair z).1 [] none
  rw [List.append_nil] at h3
  have h4 := phase4 O' R' ((splitPair z).1.take (splitPair z).2.length).reverse none
  have h5 := phase5 R' ((splitPair z).1.take (splitPair z).2.length).reverse none
  have h6 := phase6 ((splitPair z).1.take (splitPair z).2.length).reverse [] none
  rw [List.reverse_reverse, List.append_nil] at h6
  have h7 : rn 1 (cfg 7 none [] (Tk z) [] []) = some ⟨none, none, ![[], Tk z, [], []]⟩ :=
    rn_succ_step (s7_halt none (Tk z))
  have c1 := rn_trans h1 h2
  have c2 := rn_trans c1 h3
  have c3 := rn_trans c2 h4
  have c4 := rn_trans c3 h5
  have c5 := rn_trans c4 h6
  have c6 := rn_trans c5 h7
  refine ⟨_, ?_, c6⟩
  have hrev : (splitPair z).1.reverse.length = (splitPair z).1.length := List.length_reverse
  have hrev2 : (((splitPair z).1.take (splitPair z).2.length).reverse).length ≤
      (splitPair z).1.length := by
    simp only [List.length_reverse, List.length_take]
    omega
  simp only [List.length_reverse] at hrev hrev2 ⊢
  omega

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) Tk where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 10
  outputsFun z := by
    have hs := (gen z).choose_spec.1
    have he := (gen z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(gen z).choose] (some (initList tm z)) =
        some (haltList tm (Tk z)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (Tk z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ T : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
    ∀ x u : List Bool, T (pair x u) = x.take u.length :=
  ⟨Tk, ⟨machine⟩, fun x u => by
    show (splitPair (pair x u)).1.take (splitPair (pair x u)).2.length = _
    rw [splitPair_pair]⟩

end MPP.Solutions.Pnp136
