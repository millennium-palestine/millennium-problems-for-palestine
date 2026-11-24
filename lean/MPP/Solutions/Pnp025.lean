import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp025

open Turing MPP.PvsNP

/-- Program of the suffix machine. Label 0 reads two symbols per step, pushing equal doubled bits
onto the accumulator (stack 2); at the separator it moves to label 1. Label 1 empties the
accumulator. Label 2 moves the remaining input to the accumulator, which reverses it. Label 3 moves
the accumulator to the output stack, which reverses it back, and halts. -/
def prog : Fin 4 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun s h => (h, s.2)) (.pop 0 (fun s h => (s.1, h))
      (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
        (.push 2 (fun s => s.1.getD false) (.goto fun _ => 0))
        (.goto fun _ => 1)))
  | 1 => .peek 2 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.pop 2 (fun s _ => s) (.goto fun _ => 1))
        (.goto fun _ => 2))
  | 2 => .peek 0 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.pop 0 (fun s _ => s) (.push 2 (fun s => s.2.getD false) (.goto fun _ => 2)))
        (.goto fun _ => 3))
  | 3 => .peek 2 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.pop 2 (fun s _ => s) (.push 1 (fun s => s.2.getD false) (.goto fun _ => 3)))
        (.load (fun _ => (none, none)) .halt))

/-- The suffix machine: stacks `0` (input), `1` (output), `2` (accumulator). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, input stack `R`, output stack `O`, accumulator `B`. -/
def cfg (l : Fin 4) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, B]⟩

theorem step0_match (a : Bool) (v : Option Bool × Option Bool) (R A : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) [] A) = some (cfg 0 (some a, some a) R [] (a :: A)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_mismatch (a b : Bool) (hab : a ≠ b) (v : Option Bool × Option Bool) (R A : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) [] A) = some (cfg 1 (some a, some b) R [] A) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem step0_one (a : Bool) (v : Option Bool × Option Bool) (A : List Bool) :
    TM2.step prog (cfg 0 v [a] [] A) = some (cfg 1 (some a, none) [] [] A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : Option Bool × Option Bool) (A : List Bool) :
    TM2.step prog (cfg 0 v [] [] A) = some (cfg 1 (none, none) [] [] A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_pop (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 1 v R O (a :: B)) = some (cfg 1 (v.1, some a) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_end (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 1 v R O []) = some (cfg 2 (v.1, none) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_push (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 2 v (a :: R) O B) = some (cfg 2 (v.1, some a) R O (a :: B)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_end (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 2 v [] O B) = some (cfg 3 (v.1, none) [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step3_push (a : Bool) (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 3 v [] O (a :: B)) = some (cfg 3 (v.1, some a) [] (a :: O) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step3_end (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 3 v [] O []) = some ⟨none, (none, none), ![[], O, []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem rn_halt (t : ℕ)
    (H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool))
    (hH : H.l = none) : rn (t + 1) H = none := by
  unfold rn
  rw [Function.iterate_succ_apply]
  have hs : TM2.step prog H = none := by
    obtain ⟨l, v, S⟩ := H
    simp only at hH
    subst hH
    rfl
  simp only [Option.bind_some, hs]
  exact Function.iterate_fixed rfl t

theorem phase1 (x w A : List Bool) (v : Option Bool × Option Bool) :
    rn (x.length + 1) (cfg 0 v (MPP.PvsNP.pair x w) [] A) =
      some (cfg 1 (some false, some true) w [] (x.reverse ++ A)) := by
  induction x generalizing A v with
  | nil =>
    have hp : MPP.PvsNP.pair [] w = false :: true :: w := by simp [MPP.PvsNP.pair]
    rw [hp, show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_mismatch false true (by decide) v w A)]
    simp [rn]
  | cons a x ih =>
    have hp : MPP.PvsNP.pair (a :: x) w = a :: a :: MPP.PvsNP.pair x w := by
      simp [MPP.PvsNP.pair, List.flatMap_cons]
    rw [hp, rn_succ_step (step0_match a v (MPP.PvsNP.pair x w) A)]
    rw [show (a :: x).length = x.length + 1 from rfl]
    rw [ih (a :: A) (some a, some a)]
    simp [List.reverse_cons, List.append_assoc]

theorem drainAcc (L O R : List Bool) (v : Option Bool × Option Bool) :
    rn (L.length + 1) (cfg 1 v R O L) = some (cfg 2 (v.1, none) R O []) := by
  induction L generalizing v with
  | nil =>
    rw [rn_succ_step (step1_end v R O)]
    simp [rn]
  | cons a L ih =>
    rw [rn_succ_step (step1_pop a v R O L)]
    rw [show (a :: L).length = L.length + 1 from rfl]
    rw [ih (v.1, some a)]

theorem copyIn (R B O : List Bool) (v : Option Bool × Option Bool) :
    rn (R.length + 1) (cfg 2 v R O B) = some (cfg 3 (v.1, none) [] O (R.reverse ++ B)) := by
  induction R generalizing B v with
  | nil =>
    rw [rn_succ_step (step2_end v O B)]
    simp [rn]
  | cons a R ih =>
    rw [rn_succ_step (step2_push a v R O B)]
    rw [show (a :: R).length = R.length + 1 from rfl]
    rw [ih (a :: B) (v.1, some a)]
    simp [List.reverse_cons, List.append_assoc]

theorem copyOut (L O : List Bool) (v : Option Bool × Option Bool) :
    rn (L.length + 1) (cfg 3 v [] O L) = some ⟨none, (none, none), ![[], L.reverse ++ O, []]⟩ := by
  induction L generalizing O v with
  | nil =>
    rw [rn_succ_step (step3_end v O)]
    simp [rn]
  | cons a L ih =>
    rw [rn_succ_step (step3_push a v O L)]
    rw [show (a :: L).length = L.length + 1 from rfl]
    rw [ih (a :: O) (v.1, some a)]
    simp [List.reverse_cons, List.append_assoc]

/-- For any input, the first phase halts after at most `|R| + 1` steps. -/
theorem phase1_gen : ∀ (R A : List Bool) (v : Option Bool × Option Bool),
    ∃ s, s ≤ R.length + 1 ∧ ∃ (v' : Option Bool × Option Bool) (R' A' : List Bool),
      rn s (cfg 0 v R [] A) = some (cfg 1 v' R' [] A') ∧
        R'.length + A'.length ≤ R.length + A.length
  | [], A, v => ⟨1, by simp, (none, none), [], A, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_nil v A)]; simp [rn], by simp⟩
  | [a], A, v => ⟨1, by simp, (some a, none), [], A, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_one a v A)]; simp [rn], by simp⟩
  | a :: b :: R, A, v => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, hs, v', R', A', h, hl⟩ := phase1_gen R (a :: A) (some a, some a)
      refine ⟨s + 1, by simp only [List.length_cons]; omega, v', R', A', ?_, by
        simp only [List.length_cons] at hl ⊢; omega⟩
      rw [rn_succ_step (step0_match a v R A)]
      exact h
    · exact ⟨1, by simp, (some a, some b), R, A, by
        rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_mismatch a b hab v R A)]
        simp [rn], by simp only [List.length_cons]; omega⟩

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, (none, none), ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

/-- Every input is processed in at most `3|z| + 5` steps, to some output. -/
theorem gen (z : List Bool) : ∃ O : List Bool, ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], O, []]⟩ := by
  obtain ⟨s1, hs1, v', R', A', h1, hl⟩ := phase1_gen z [] (none, none)
  have h2 := drainAcc A' [] R' v'
  have h3 := copyIn R' [] [] (v'.1, none)
  simp only [List.append_nil] at h3
  have h4 := copyOut R'.reverse [] (v'.1, none)
  simp only [List.reverse_reverse, List.append_nil] at h4
  have hA := (rn_add (n := A'.length + 1) h1).trans h2
  have hB := (rn_add (n := R'.length + 1) hA).trans h3
  have hC := (rn_add (n := R'.reverse.length + 1) hB).trans h4
  refine ⟨R', (R'.reverse.length + 1) + ((R'.length + 1) + ((A'.length + 1) + s1)), ?_, hC⟩
  simp only [List.length_reverse, List.length_nil, add_zero] at hl ⊢
  omega

theorem rn_halted {H K : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)}
    {d : ℕ} (hH : H.l = none) (h : rn d H = some K) : d = 0 ∧ H = K := by
  cases d with
  | zero =>
    simp only [rn, Function.iterate_zero, id_eq, Option.some.injEq] at h
    exact ⟨rfl, h⟩
  | succ d =>
    rw [rn_halt d H hH] at h
    cases h

theorem rn_unique {c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool)}
    {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none), ![[], O, []]⟩)
    (ht : rn t c = some ⟨none, (none, none), ![[], P, []]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this.symm

/-- The suffix map: the output of the machine on the input. -/
noncomputable def suf (z : List Bool) : List Bool := (gen z).choose

theorem suf_spec (z : List Bool) : ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], suf z, []]⟩ :=
  (gen z).choose_spec

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) suf where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 5
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[(suf_spec z).choose]
        (some (initList tm z)) = some (haltList tm (suf z)) := by
      rw [initList_eq, haltList_eq]
      exact (suf_spec z).choose_spec.2
    refine ⟨⟨(suf_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (suf z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have := (suf_spec z).choose_spec.1
      omega

theorem main : ∃ e : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) e) ∧
      ∀ x w : List Bool, e (MPP.PvsNP.pair x w) = w := by
  refine ⟨suf, ⟨machine⟩, fun x w => ?_⟩
  have h1 := phase1 x w [] (none, none)
  simp only [List.append_nil] at h1
  have h2 := drainAcc x.reverse [] w (some false, some true)
  simp only [List.length_reverse] at h2
  have hA := (rn_add (n := x.length + 1) h1).trans h2
  have h3 := copyIn w [] [] (some false, none)
  simp only [List.append_nil] at h3
  have hB := (rn_add (n := w.length + 1) hA).trans h3
  have h4 := copyOut w.reverse [] (some false, none)
  have hC := (rn_add (n := w.reverse.length + 1) hB).trans h4
  obtain ⟨s, -, hs⟩ := suf_spec (MPP.PvsNP.pair x w)
  have := rn_unique hs hC
  simpa using this

end MPP.Solutions.Pnp025
