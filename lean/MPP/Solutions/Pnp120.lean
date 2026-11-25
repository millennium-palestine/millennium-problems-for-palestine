import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp120

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

/-- Program of the drop map. Stack 0 is the input, stack 1 the output, stack 2 an accumulator.
Label 0 pops the first symbol of a doubled pair. Label 1 pops the second one: a doubled pair
pushes its bit onto the accumulator and returns to label 0; otherwise the separator has been read
and the machine moves to label 2. Label 2 moves the accumulator onto the output, which reverses
it back to the order of the input. Label 3 pops one symbol of the rest of the input and one
symbol of the output for each such symbol, which drops them from the output. Label 4 halts. -/
def prog : Fin 5 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)
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
        (.pop 1 (fun _ h => h) (.goto fun _ => 3))
        (.goto fun _ => 4))
  | 4 => .load (fun _ => none) .halt

/-- The drop map as a finite machine: stacks `0` (input), `1` (output), `2` (accumulator). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool
  initialState := none
  m := prog

/-- Configuration with label `l`, state `v`, input `R`, output `O`, accumulator `B`. -/
def cfg (l : Fin 5) (v : Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool) :=
  ⟨some l, v, ![R, O, B]⟩

theorem s0_cons (v : Option Bool) (a : Bool) (R O B : List Bool) :
    TM2.step prog (cfg 0 v (a :: R) O B) = some (cfg 1 (some a) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s0_nil (v : Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 0 v [] O B) = some (cfg 1 none [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s1_eq (a : Bool) (R O B : List Bool) :
    TM2.step prog (cfg 1 (some a) (a :: R) O B) = some (cfg 0 (some a) R O (a :: B)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg, dbl] <;> (funext j; fin_cases j <;> simp)

theorem s1_ne (a b : Bool) (h : a ≠ b) (R O B : List Bool) :
    TM2.step prog (cfg 1 (some a) (b :: R) O B) = some (cfg 2 none R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg, dbl, h] <;> (funext j; fin_cases j <;> simp)

theorem s1_nil (v : Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 1 v [] O B) = some (cfg 2 none [] O B) := by
  cases v <;> simp [TM2.step, TM2.stepAux, prog, cfg, dbl] <;> (funext j; fin_cases j <;> simp)

theorem s2_cons (a : Bool) (v : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 2 v R O (a :: B)) = some (cfg 2 (some a) R (a :: O) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s2_nil (v : Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 2 v R O []) = some (cfg 3 none R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s3_cons (v : Option Bool) (a : Bool) (u O B : List Bool) :
    TM2.step prog (cfg 3 v (a :: u) O B) = some (cfg 3 O.head? u O.tail B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s3_nil (v : Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 3 v [] O B) = some (cfg 4 none [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

theorem s4_halt (v : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 4 v R O B) = some ⟨none, none, ![R, O, B]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext j; fin_cases j <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem rn_trans {m n : ℕ}
    {c c' c'' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool)}
    (h1 : rn m c = some c') (h2 : rn n c' = some c'') : rn (n + m) c = some c'' := by
  rw [rn_add h1]
  exact h2

/-- Phase 1: the doubled pairs of the input are read; their bits go onto the accumulator in
reverse order, and the rest of the input after the first non-doubled pair is left on stack 0. -/
theorem phase1 : ∀ (z B : List Bool) (v : Option Bool),
    ∃ s, s ≤ z.length + 2 ∧
      rn s (cfg 0 v z [] B) = some (cfg 2 none (splitPair z).2 [] ((splitPair z).1.reverse ++ B))
  | [], B, v => ⟨2, by simp, by
      show rn (0 + 1 + 1) (cfg 0 v [] [] B) = _
      rw [rn_succ_step (s0_nil v [] B), rn_succ_step (s1_nil none [] B)]
      simp [rn, splitPair]⟩
  | [a], B, v => ⟨2, by simp, by
      show rn (0 + 1 + 1) (cfg 0 v [a] [] B) = _
      rw [rn_succ_step (s0_cons v a [] [] B), rn_succ_step (s1_nil (some a) [] B)]
      simp [rn, splitPair]⟩
  | a :: b :: rest, B, v => by
      by_cases h : a = b
      · subst h
        obtain ⟨s, hs, hrun⟩ := phase1 rest (a :: B) (some a)
        refine ⟨s + 1 + 1, by simp only [List.length_cons]; omega, ?_⟩
        show rn (s + 1 + 1) (cfg 0 v (a :: a :: rest) [] B) = _
        rw [rn_succ_step (s0_cons v a (a :: rest) [] B), rn_succ_step (s1_eq a rest [] B), hrun,
          splitPair_eq]
        simp [List.reverse_cons, List.append_assoc]
      · refine ⟨2, by simp, ?_⟩
        show rn (0 + 1 + 1) (cfg 0 v (a :: b :: rest) [] B) = _
        rw [rn_succ_step (s0_cons v a (b :: rest) [] B), rn_succ_step (s1_ne a b h rest [] B),
          splitPair_ne a b h]
        simp [rn]

/-- Phase 2: the accumulator is moved onto the output, which reverses it. -/
theorem phase2 : ∀ (B O R : List Bool) (v : Option Bool),
    rn (B.length + 1) (cfg 2 v R O B) = some (cfg 3 none R (B.reverse ++ O) [])
  | [], O, R, v => by
      show rn (0 + 1) (cfg 2 v R O []) = _
      rw [rn_succ_step (s2_nil v R O)]
      simp [rn]
  | a :: B, O, R, v => by
      show rn (B.length + 1 + 1) (cfg 2 v R O (a :: B)) = _
      rw [rn_succ_step (s2_cons a v R O B), phase2 B (a :: O) R (some a)]
      simp [List.reverse_cons, List.append_assoc]

theorem tail_drop_eq (O : List Bool) (m : ℕ) : O.tail.drop m = O.drop (m + 1) := by
  cases O <;> simp

/-- Phase 3: one symbol of the rest of the input is matched with one symbol of the output, which
is dropped; the rest of the input is consumed in `|u| + 2` steps in total. -/
theorem phase3 : ∀ (u O : List Bool) (v : Option Bool),
    rn (u.length + 2) (cfg 3 v u O []) = some ⟨none, none, ![[], O.drop u.length, []]⟩
  | [], O, v => by
      show rn (0 + 1 + 1) (cfg 3 v [] O []) = _
      rw [rn_succ_step (s3_nil v O []), rn_succ_step (s4_halt none [] O [])]
      simp [rn]
  | a :: u, O, v => by
      have ih := phase3 u O.tail O.head?
      show rn (u.length + 2 + 1) (cfg 3 v (a :: u) O []) = _
      rw [rn_succ_step (s3_cons v a u O []), ih]
      simp

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 none z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (j : Fin 3) => ?_
  fin_cases j <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, none, ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (j : Fin 3) => ?_
  fin_cases j <;> simp [tm]

/-- The drop map, defined on every input as the machine computes it. -/
def D (z : List Bool) : List Bool := (splitPair z).1.drop (splitPair z).2.length

/-- Every input is mapped by the machine in at most `2|z| + 5` steps. -/
theorem gen (z : List Bool) : ∃ s, s ≤ 2 * z.length + 5 ∧
    rn s (cfg 0 none z [] []) = some ⟨none, none, ![[], D z, []]⟩ := by
  obtain ⟨s1, hs1, h1⟩ := phase1 z [] none
  rw [List.append_nil] at h1
  have h2 := phase2 (splitPair z).1.reverse [] (splitPair z).2 none
  rw [List.append_nil, List.reverse_reverse] at h2
  have h3 := phase3 (splitPair z).2 (splitPair z).1 none
  have h12 := rn_trans h1 h2
  refine ⟨(splitPair z).2.length + 2 + ((splitPair z).1.reverse.length + 1 + s1), ?_, rn_trans h12 h3⟩
  have hl := splitPair_len z
  simp only [List.length_reverse] at h2 ⊢
  omega

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) D where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 5
  outputsFun z := by
    have hs := (gen z).choose_spec.1
    have he := (gen z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(gen z).choose] (some (initList tm z)) =
        some (haltList tm (D z)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (D z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ D : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) D) ∧
    ∀ x u : List Bool, D (pair x u) = x.drop u.length :=
  ⟨D, ⟨machine⟩, fun x u => by
    show (splitPair (pair x u)).1.drop (splitPair (pair x u)).2.length = _
    rw [splitPair_pair]⟩

end MPP.Solutions.Pnp120
