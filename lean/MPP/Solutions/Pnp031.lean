import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp031

open MPP.PvsNP Turing

/-- Program of the unary-addition machine. Label 0 reads two symbols of the input stack per step:
a doubled bit pushes `false` onto the output (stack 1) and repeats; two unequal symbols form the
separator `[false, true]`, and the machine moves to label 1. Label 1 pops the rest of the input,
pushing `false` for each symbol, and halts when the input is empty. -/
def prog : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun s h => (h, s.2)) (.pop 0 (fun s h => (s.1, h))
      (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
        (.push 1 (fun _ => false) (.goto fun _ => 0))
        (.goto fun _ => 1)))
  | 1 => .pop 0 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 1 (fun _ => false) (.goto fun _ => 1))
        (.load (fun _ => (none, none)) .halt))

/-- The unary-addition machine: stacks `0` (input) and `1` (output). -/
def tm : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, input stack `R` and output stack `O`. -/
def cfg (l : Fin 2) (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O]⟩

theorem step0_match (a : Bool) (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) O) = some (cfg 0 (some a, some a) R (false :: O)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_mismatch (a b : Bool) (hab : a ≠ b) (v : Option Bool × Option Bool)
    (R O : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O) = some (cfg 1 (some a, some b) R O) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem step0_one (a : Bool) (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 0 v [a] O) = some (cfg 1 (some a, none) [] O) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 0 v [] O) = some (cfg 1 (none, none) [] O) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_push (a : Bool) (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 1 v (a :: R) O) = some (cfg 1 (some a, v.2) R (false :: O)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_end (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 1 v [] O) = some ⟨none, (none, none), ![[], O]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Phase 1 on a pair encoding: the doubled part of `u` is consumed, one `false` per doubled
pair, and the machine stops at the separator with the rest `R` still on the input. -/
theorem phase1 (u R O : List Bool) (v : Option Bool × Option Bool) :
    rn (u.length + 1) (cfg 0 v (pair u R) O) =
      some (cfg 1 (some false, some true) R (List.replicate u.length false ++ O)) := by
  induction u generalizing O v with
  | nil =>
    have hp : pair [] R = false :: true :: R := by simp [pair]
    rw [hp, show ([] : List Bool).length + 1 = 0 + 1 from rfl,
      rn_succ_step (step0_mismatch false true (by decide) v R O)]
    simp [rn]
  | cons a u ih =>
    have hp : pair (a :: u) R = a :: a :: pair u R := by
      simp [pair, List.flatMap_cons]
    rw [hp, show (a :: u).length + 1 = (u.length + 1) + 1 from rfl,
      rn_succ_step (step0_match a v (pair u R) O)]
    rw [ih (false :: O) (some a, some a)]
    simp [List.replicate_succ', List.append_assoc]

theorem phase2 (R O : List Bool) (v : Option Bool × Option Bool) :
    rn (R.length + 1) (cfg 1 v R O) =
      some ⟨none, (none, none), ![[], List.replicate R.length false ++ O]⟩ := by
  induction R generalizing O v with
  | nil =>
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step1_end v O)]
    simp [rn]
  | cons a R ih =>
    rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl,
      rn_succ_step (step1_push a v R O)]
    rw [ih (false :: O) (some a, v.2)]
    simp [List.replicate_succ', List.append_assoc]

/-- On a pair encoding the machine outputs `|u|` blocks of falses, then `|R|` more falses. -/
theorem run (u R : List Bool) :
    rn ((R.length + 1) + (u.length + 1)) (cfg 0 (none, none) (pair u R) []) =
      some ⟨none, (none, none), ![[], List.replicate R.length false ++ List.replicate u.length false]⟩ := by
  have h1 := phase1 u R [] (none, none)
  rw [rn_add (n := R.length + 1) (by simpa using h1)]
  simpa using phase2 R (List.replicate u.length false) (some false, some true)

/-- Phase 1 for an arbitrary input: it stops after at most `|z| + 1` steps, with the rest of the
input no longer than `z`. -/
theorem phase1_gen : ∀ (z O : List Bool) (st : Option Bool × Option Bool),
    ∃ s, s ≤ z.length + 1 ∧ ∃ (st' : Option Bool × Option Bool) (R O' : List Bool),
      rn s (cfg 0 st z O) = some (cfg 1 st' R O') ∧ R.length ≤ z.length
  | [], O, st => ⟨1, by simp, (none, none), [], O,
      (rn_succ_step (n := 0) (step0_nil st O)).trans (by simp [rn]), by simp⟩
  | [a], O, st => ⟨1, by simp, (some a, none), [], O,
      (rn_succ_step (n := 0) (step0_one a st O)).trans (by simp [rn]), by simp⟩
  | a :: b :: R, O, st => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, hs, st', R', O', h, hl⟩ := phase1_gen R (false :: O) (some a, some a)
      refine ⟨s + 1, by simp only [List.length_cons] at hs ⊢; omega, st', R', O', ?_, by
        simp only [List.length_cons] at hl ⊢; omega⟩
      rw [rn_succ_step (step0_match a st R O)]
      exact h
    · exact ⟨1, by simp, (some a, some b), R, O,
        (rn_succ_step (n := 0) (step0_mismatch a b hab st R O)).trans (by simp [rn]),
        by simp only [List.length_cons]; omega⟩

/-- Every input halts after at most `2|z| + 3` steps, to some output. -/
theorem gen (z : List Bool) : ∃ O : List Bool, ∃ s, s ≤ 2 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z []) = some ⟨none, (none, none), ![[], O]⟩ := by
  obtain ⟨s1, hs1, st', R', O', h1, hl⟩ := phase1_gen z [] (none, none)
  refine ⟨List.replicate R'.length false ++ O', (R'.length + 1) + s1, ?_, ?_⟩
  · omega
  · rw [rn_add (n := R'.length + 1) h1]
    exact phase2 R' O' st'

theorem rn_halted {H K : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)}
    {d : ℕ} (hH : H.l = none) (h : rn d H = some K) : d = 0 ∧ H = K := by
  cases d with
  | zero =>
    simp only [rn, Function.iterate_zero, id_eq, Option.some.injEq] at h
    exact ⟨rfl, h⟩
  | succ d =>
    have hs : TM2.step prog H = none := by
      obtain ⟨l, v, S⟩ := H
      simp only at hH
      subst hH
      rfl
    unfold rn at h
    rw [Function.iterate_succ_apply] at h
    simp [hs] at h
    have hfix : (fun o => o.bind (TM2.step prog))^[d] none = none :=
      Function.iterate_fixed rfl d
    rw [hfix] at h
    cases h

theorem rn_unique {c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool)}
    {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none), ![[], O]⟩)
    (ht : rn t c = some ⟨none, (none, none), ![[], P]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this.symm

/-- The machine's output on the input. -/
noncomputable def add (z : List Bool) : List Bool := (gen z).choose

theorem add_spec (z : List Bool) : ∃ s, s ≤ 2 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z []) = some ⟨none, (none, none), ![[], add z]⟩ :=
  (gen z).choose_spec

theorem add_pair (u R : List Bool) :
    add (pair u R) = List.replicate (u.length + R.length) false := by
  obtain ⟨s, -, hs⟩ := add_spec (pair u R)
  have hB := run u R
  have := rn_unique hs hB
  rw [this, add_comm, List.replicate_add]

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) : haltList tm O = ⟨none, (none, none), ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) add where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun z := by
    have hs := (add_spec z).choose_spec.1
    have he := (add_spec z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(add_spec z).choose]
        (some (initList tm z)) = some (haltList tm (add z)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(add_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (add z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ E : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) E) ∧
    ∀ u v : List Bool, E (pair u v) = List.replicate (u.length + v.length) false :=
  ⟨add, ⟨machine⟩, fun u v => add_pair u v⟩

end MPP.Solutions.Pnp031
