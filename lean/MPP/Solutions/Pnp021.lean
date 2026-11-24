import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp021

open Turing

/-- Program of the decoder. Label 0 reads two symbols of the input stack per step and either
pushes the doubled bit onto the accumulator (stack 2) or, at the separator, moves to label 1.
Label 1 moves the accumulator onto the output stack (stack 1), which reverses it back. Label 2
empties the input stack and halts. -/
def prog : Fin 3 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun s h => (h, s.2)) (.pop 0 (fun s h => (s.1, h))
      (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
        (.push 2 (fun s => s.1.getD false) (.goto fun _ => 0))
        (.goto fun _ => 1)))
  | 1 => .peek 2 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.pop 2 (fun s _ => s) (.push 1 (fun s => s.2.getD false) (.goto fun _ => 1)))
        (.goto fun _ => 2))
  | 2 => .peek 0 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.pop 0 (fun s _ => s) (.goto fun _ => 2))
        (.load (fun _ => (none, none)) .halt))

/-- The decoder as a finite machine: stacks `0` (input), `1` (output), `2` (accumulator). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, input stack `R`, output stack `O`, accumulator `B`. -/
def cfg (l : Fin 3) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool) :=
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

theorem step1_push (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 1 v R O (a :: B)) = some (cfg 1 (v.1, some a) R (a :: O) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_end (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 1 v R O []) = some (cfg 2 (v.1, none) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_push (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 2 v (a :: R) O B) = some (cfg 2 (v.1, some a) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_end (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 2 v [] O B) = some ⟨none, (none, none), ![[], O, B]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem rn_halt (t : ℕ)
    (H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool))
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

theorem phase2 (L O R : List Bool) (v : Option Bool × Option Bool) :
    rn (L.length + 1) (cfg 1 v R O L) = some (cfg 2 (v.1, none) R (L.reverse ++ O) []) := by
  induction L generalizing O v with
  | nil =>
    rw [rn_succ_step (step1_end v R O)]
    simp [rn]
  | cons a L ih =>
    rw [rn_succ_step (step1_push a v R O L)]
    rw [show (a :: L).length = L.length + 1 from rfl]
    rw [ih (a :: O) (v.1, some a)]
    simp [List.reverse_cons, List.append_assoc]

theorem phase3 (R O : List Bool) (v : Option Bool × Option Bool) :
    rn (R.length + 1) (cfg 2 v R O []) = some ⟨none, (none, none), ![[], O, []]⟩ := by
  induction R generalizing v with
  | nil =>
    rw [rn_succ_step (step2_end v O [])]
    simp [rn]
  | cons a R ih =>
    rw [rn_succ_step (step2_push a v R O [])]
    rw [show (a :: R).length = R.length + 1 from rfl]
    rw [ih (v.1, some a)]

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

/-- Every input is decoded by the machine in at most `2|z| + 3` steps, to some output. -/
theorem gen (z : List Bool) : ∃ O : List Bool, ∃ s, s ≤ 2 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], O, []]⟩ := by
  obtain ⟨s1, hs1, v', R', A', h1, hl⟩ := phase1_gen z [] (none, none)
  have h2 := phase2 A' [] R' v'
  have h3 := phase3 R' (A'.reverse ++ []) (v'.1, none)
  have hA : rn ((A'.length + 1) + s1) (cfg 0 (none, none) z [] []) =
      some (cfg 2 (v'.1, none) R' (A'.reverse ++ []) []) := by
    rw [rn_add h1]
    simpa using h2
  have hB := rn_add (n := R'.length + 1) hA
  refine ⟨A'.reverse, (R'.length + 1) + ((A'.length + 1) + s1), ?_, ?_⟩
  · simp only [List.length_nil, add_zero] at hl
    omega
  · rw [hB, h3]
    simp

theorem rn_halted {H K : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)}
    {d : ℕ} (hH : H.l = none) (h : rn d H = some K) : d = 0 ∧ H = K := by
  cases d with
  | zero =>
    simp only [rn, Function.iterate_zero, id_eq, Option.some.injEq] at h
    exact ⟨rfl, h⟩
  | succ d =>
    rw [rn_halt d H hH] at h
    cases h

theorem rn_unique {c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool)}
    {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none), ![[], O, []]⟩)
    (ht : rn t c = some ⟨none, (none, none), ![[], P, []]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool × Option Bool) =>
      H.stk 1) hK
    simpa using this.symm

/-- The decoder: the output of the machine on the input. -/
noncomputable def dec (z : List Bool) : List Bool := (gen z).choose

theorem dec_spec (z : List Bool) : ∃ s, s ≤ 2 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], dec z, []]⟩ :=
  (gen z).choose_spec

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) dec where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun z := by
    have hs := (dec_spec z).choose_spec.1
    have he := (dec_spec z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(dec_spec z).choose]
        (some (initList tm z)) = some (haltList tm (dec z)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(dec_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (dec z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ d : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) d) ∧
      ∀ x w : List Bool, d (MPP.PvsNP.pair x w) = x := by
  refine ⟨dec, ⟨machine⟩, fun x w => ?_⟩
  have h1 := phase1 x w [] (none, none)
  simp only [List.append_nil] at h1
  have h2 := phase2 x.reverse [] w (some false, some true)
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h2
  have hA := (rn_add (n := x.length + 1) h1).trans h2
  have hB := (rn_add (n := w.length + 1) hA).trans (phase3 w x _)
  obtain ⟨s, -, hs⟩ := dec_spec (MPP.PvsNP.pair x w)
  exact rn_unique hs hB

end MPP.Solutions.Pnp021
