import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp032

open MPP.PvsNP Turing

/-- Program of the unary-multiplication machine. Stacks: `0` input, `1` output, `2` counter `U`,
`3` copy `V` of the second factor, `4` temporary `T`. The state holds the last symbols read.

* Label 0 reads two symbols: a doubled bit pushes `false` onto `U` and repeats; otherwise the
  separator has been read and the machine moves to label 1.
* Label 1 moves the rest of the input (the second factor) onto `V`, one symbol per step.
* Label 2 pops one counter symbol. If there is one, go to label 3; otherwise to label 5.
* Label 3 pops a symbol of `V`. If there is one, push `false` onto the output, move the symbol
  onto `T`, and repeat; otherwise go to label 4.
* Label 4 moves the symbols of `T` back onto `V`, and then returns to label 2.
* Label 5 empties `V`, then halts. -/
def prog : Fin 6 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun s h => (h, s.2)) (.pop 0 (fun s h => (s.1, h))
      (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
        (.push 2 (fun _ => false) (.goto fun _ => 0))
        (.goto fun _ => 1)))
  | 1 => .pop 0 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 3 (fun s => s.1.getD false) (.goto fun _ => 1))
        (.goto fun _ => 2))
  | 2 => .pop 2 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.goto fun _ => 3)
        (.goto fun _ => 5))
  | 3 => .pop 3 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 1 (fun _ => false) (.push 4 (fun s => s.1.getD false) (.goto fun _ => 3)))
        (.goto fun _ => 4))
  | 4 => .pop 4 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 3 (fun s => s.1.getD false) (.goto fun _ => 4))
        (.goto fun _ => 2))
  | 5 => .pop 3 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.goto fun _ => 5)
        (.load (fun _ => (none, none)) .halt))

/-- The unary-multiplication machine: five stacks, as described in `prog`. -/
def tm : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 6
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input), `O` (output), `U`, `V`, `T`. -/
def cfg (l : Fin 6) (v : Option Bool × Option Bool) (R O U V T : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, U, V, T]⟩

theorem s0_match (a : Bool) (v : Option Bool × Option Bool) (R O U V T : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) O U V T) =
      some (cfg 0 (some a, some a) R O (false :: U) V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s0_mismatch (a b : Bool) (hab : a ≠ b) (v : Option Bool × Option Bool)
    (R O U V T : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O U V T) =
      some (cfg 1 (some a, some b) R O U V T) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem s0_one (a : Bool) (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 0 v [a] O U V T) = some (cfg 1 (some a, none) [] O U V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s0_nil (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 0 v [] O U V T) = some (cfg 1 (none, none) [] O U V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s1_some (b : Bool) (v : Option Bool × Option Bool) (R O U V T : List Bool) :
    TM2.step prog (cfg 1 v (b :: R) O U V T) = some (cfg 1 (some b, v.2) R O U (b :: V) T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s1_none (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 1 v [] O U V T) = some (cfg 2 (none, v.2) [] O U V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s2_some (u : Bool) (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 2 v [] O (u :: U) V T) = some (cfg 3 (some u, v.2) [] O U V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s2_none (v : Option Bool × Option Bool) (O V T : List Bool) :
    TM2.step prog (cfg 2 v [] O [] V T) = some (cfg 5 (none, v.2) [] O [] V T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s3_some (b : Bool) (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 3 v [] O U (b :: V) T) =
      some (cfg 3 (some b, v.2) [] (false :: O) U V (b :: T)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s3_none (v : Option Bool × Option Bool) (O U T : List Bool) :
    TM2.step prog (cfg 3 v [] O U [] T) = some (cfg 4 (none, v.2) [] O U [] T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s4_some (b : Bool) (v : Option Bool × Option Bool) (O U V T : List Bool) :
    TM2.step prog (cfg 4 v [] O U V (b :: T)) = some (cfg 4 (some b, v.2) [] O U (b :: V) T) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s4_none (v : Option Bool × Option Bool) (O U V : List Bool) :
    TM2.step prog (cfg 4 v [] O U V []) = some (cfg 2 (none, v.2) [] O U V []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s5_some (b : Bool) (v : Option Bool × Option Bool) (O V : List Bool) :
    TM2.step prog (cfg 5 v [] O [] (b :: V) []) = some (cfg 5 (some b, v.2) [] O [] V []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem s5_none (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 5 v [] O [] [] []) = some ⟨none, (none, none), ![[], O, [], [], []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Phase A on a pair encoding: `|u| + 1` steps, one `false` pushed onto `U` per doubled bit. -/
theorem phaseA (u v O U V T : List Bool) (st : Option Bool × Option Bool) :
    rn (u.length + 1) (cfg 0 st (pair u v) O U V T) =
      some (cfg 1 (some false, some true) v O (List.replicate u.length false ++ U) V T) := by
  induction u generalizing U st with
  | nil =>
    have hp : pair [] v = false :: true :: v := by simp [pair]
    rw [hp, show ([] : List Bool).length + 1 = 0 + 1 from rfl,
      rn_succ_step (s0_mismatch false true (by decide) st v O U V T)]
    simp [rn]
  | cons a u ih =>
    have hp : pair (a :: u) v = a :: a :: pair u v := by
      simp [pair, List.flatMap_cons]
    rw [hp, show (a :: u).length + 1 = (u.length + 1) + 1 from rfl,
      rn_succ_step (s0_match a st (pair u v) O U V T)]
    rw [ih (false :: U) (some a, some a)]
    simp [List.replicate_succ', List.append_assoc]

/-- Phase A for an arbitrary input: at most `|z| + 1` steps, the rest no longer than `z`, and at
most `|z|` more counter symbols. -/
theorem phaseA_gen : ∀ (z O U V T : List Bool) (st : Option Bool × Option Bool),
    ∃ s, s ≤ z.length + 1 ∧ ∃ (st' : Option Bool × Option Bool) (R U' : List Bool),
      rn s (cfg 0 st z O U V T) = some (cfg 1 st' R O U' V T) ∧
        R.length ≤ z.length ∧ U'.length ≤ U.length + z.length
  | [], O, U, V, T, st => ⟨1, by simp, (none, none), [], U,
      (rn_succ_step (n := 0) (s0_nil st O U V T)).trans (by simp [rn]), by simp, by simp⟩
  | [a], O, U, V, T, st => ⟨1, by simp, (some a, none), [], U,
      (rn_succ_step (n := 0) (s0_one a st O U V T)).trans (by simp [rn]), by simp, by simp⟩
  | a :: b :: R, O, U, V, T, st => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, hs, st', R', U', h, hl, hU⟩ :=
        phaseA_gen R O (false :: U) V T (some a, some a)
      refine ⟨s + 1, by simp only [List.length_cons] at hs ⊢; omega, st', R', U', ?_, by
        simp only [List.length_cons] at hl ⊢; omega, by
        simp only [List.length_cons, List.length_cons] at hU ⊢; omega⟩
      rw [rn_succ_step (s0_match a st R O U V T)]
      exact h
    · exact ⟨1, by simp, (some a, some b), R, U,
        (rn_succ_step (n := 0) (s0_mismatch a b hab st R O U V T)).trans (by simp [rn]),
        by simp only [List.length_cons]; omega, by simp⟩

/-- Phase B: the rest of the input is moved onto `V`, reversed, in `|R| + 1` steps. -/
theorem phaseB : ∀ (R V O U T : List Bool) (st : Option Bool × Option Bool),
    rn (R.length + 1) (cfg 1 st R O U V T) =
      some (cfg 2 (none, st.2) [] O U (R.reverse ++ V) T)
  | [], V, O, U, T, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (s1_none st O U V T)]
    simp [rn]
  | b :: R, V, O, U, T, st => by
    rw [show (b :: R).length + 1 = (R.length + 1) + 1 from rfl,
      rn_succ_step (s1_some b st R O U V T)]
    rw [phaseB R (b :: V) O U T (some b, st.2)]
    simp [List.reverse_cons, List.append_assoc]

/-- Label 3: each symbol of `V` gives one `false` on the output and one symbol on `T`. -/
theorem inner : ∀ (V T O U : List Bool) (st : Option Bool × Option Bool),
    rn (V.length + 1) (cfg 3 st [] O U V T) =
      some (cfg 4 (none, st.2) [] (List.replicate V.length false ++ O) U [] (V.reverse ++ T))
  | [], T, O, U, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (s3_none st O U T)]
    simp [rn]
  | b :: V, T, O, U, st => by
    rw [show (b :: V).length + 1 = (V.length + 1) + 1 from rfl,
      rn_succ_step (s3_some b st O U V T)]
    rw [inner V (b :: T) (false :: O) U (some b, st.2)]
    simp [List.replicate_succ', List.reverse_cons, List.append_assoc]

/-- Label 4: `T` is moved back onto `V`, restoring the order. -/
theorem restore : ∀ (T V O U : List Bool) (st : Option Bool × Option Bool),
    rn (T.length + 1) (cfg 4 st [] O U V T) =
      some (cfg 2 (none, st.2) [] O U (T.reverse ++ V) [])
  | [], V, O, U, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (s4_none st O U V)]
    simp [rn]
  | b :: T, V, O, U, st => by
    rw [show (b :: T).length + 1 = (T.length + 1) + 1 from rfl,
      rn_succ_step (s4_some b st O U V T)]
    rw [restore T (b :: V) O U (some b, st.2)]
    simp [List.reverse_cons, List.append_assoc]

/-- Label 5: `V` is emptied and the machine halts. -/
theorem drainV : ∀ (V O : List Bool) (st : Option Bool × Option Bool),
    rn (V.length + 1) (cfg 5 st [] O [] V []) =
      some ⟨none, (none, none), ![[], O, [], [], []]⟩
  | [], O, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (s5_none st O)]
    simp [rn]
  | b :: V, O, st => by
    rw [show (b :: V).length + 1 = (V.length + 1) + 1 from rfl, rn_succ_step (s5_some b st O V)]
    exact drainV V O _

/-- The outer loop: one round per counter symbol, each costing `2|V| + 3` steps. -/
theorem outer : ∀ (U V O : List Bool) (st : Option Bool × Option Bool),
    rn (U.length * (2 * V.length + 3) + V.length + 2) (cfg 2 st [] O U V []) =
      some ⟨none, (none, none), ![[], List.replicate (U.length * V.length) false ++ O, [], [], []]⟩
  | [], V, O, st => by
    have h1 := rn_succ_step (n := V.length + 1) (s2_none st O V [])
    have h2 := drainV V O (none, st.2)
    have e : ([] : List Bool).length * (2 * V.length + 3) + V.length + 2 = (V.length + 1) + 1 := by
      simp
    rw [e, h1]
    simpa using h2
  | b :: U, V, O, st => by
    have hK : rn (2 * V.length + 3) (cfg 2 st [] O (b :: U) V []) =
        some (cfg 2 (none, st.2) [] (List.replicate V.length false ++ O) U V []) := by
      have s1 := rn_succ_step (n := (V.length + 1) + (V.length + 1)) (s2_some b st O U V [])
      have s2 := inner V [] O U (some b, st.2)
      have s3 := restore (V.reverse ++ []) [] (List.replicate V.length false ++ O) U (none, st.2)
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at s2 s3
      rw [show 2 * V.length + 3 = ((V.length + 1) + (V.length + 1)) + 1 by ring, s1,
        rn_add (n := V.length + 1) s2]
      simpa using s3
    have e : (b :: U).length * (2 * V.length + 3) + V.length + 2 =
        (U.length * (2 * V.length + 3) + V.length + 2) + (2 * V.length + 3) := by
      simp only [List.length_cons]; ring
    rw [e, rn_add hK]
    have ih := outer U V (List.replicate V.length false ++ O) (none, st.2)
    have el : (b :: U).length * V.length = U.length * V.length + V.length := by
      simp [List.length_cons, Nat.succ_mul]
    rw [el, List.replicate_add, List.append_assoc]
    exact ih

/-- Every input halts, with a unary output, after at most `2|z|^2 + 6|z| + 4` steps. -/
theorem gen (z : List Bool) : ∃ O : List Bool, ∃ s, s ≤ 2 * z.length ^ 2 + 6 * z.length + 4 ∧
    rn s (cfg 0 (none, none) z [] [] [] []) = some ⟨none, (none, none), ![[], O, [], [], []]⟩ := by
  obtain ⟨s1, hs1, st', R, U', h1, hR, hU⟩ := phaseA_gen z [] [] [] [] (none, none)
  have h2 := phaseB R [] [] U' [] st'
  have h3 := outer U' (R.reverse ++ []) [] (none, st'.2)
  simp only [List.length_nil, zero_add] at hU
  have hprod : U'.length * (2 * R.length + 3) ≤ z.length * (2 * z.length + 3) :=
    Nat.mul_le_mul hU (by omega)
  refine ⟨List.replicate (U'.length * R.length) false ++ [],
    (U'.length * (2 * R.length + 3) + R.length + 2) + ((R.length + 1) + s1), ?_, ?_⟩
  · nlinarith
  · have hA : rn ((R.length + 1) + s1) (cfg 0 (none, none) z [] [] [] []) =
        some (cfg 2 (none, st'.2) [] [] U' (R.reverse ++ []) []) := by
      rw [rn_add h1]
      exact h2
    rw [rn_add hA]
    simpa using h3

theorem rn_halted {H K : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)}
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

theorem rn_unique {c : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6) (Option Bool × Option Bool)}
    {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none), ![[], O, [], [], []]⟩)
    (ht : rn t c = some ⟨none, (none, none), ![[], P, [], [], []]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6)
      (Option Bool × Option Bool) => H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 6)
      (Option Bool × Option Bool) => H.stk 1) hK
    simpa using this.symm

/-- The unary-multiplication map, as the output of the machine. -/
noncomputable def mul (z : List Bool) : List Bool := (gen z).choose

theorem mul_spec (z : List Bool) : ∃ s, s ≤ 2 * z.length ^ 2 + 6 * z.length + 4 ∧
    rn s (cfg 0 (none, none) z [] [] [] []) = some ⟨none, (none, none), ![[], mul z, [], [], []]⟩ :=
  (gen z).choose_spec

theorem mul_pair (u v : List Bool) :
    mul (pair u v) = List.replicate (u.length * v.length) false := by
  obtain ⟨-, hs⟩ := (mul_spec (pair u v)).choose_spec
  have hA := phaseA u v [] [] [] [] (none, none)
  have hB := phaseB v [] [] (List.replicate u.length false ++ []) [] (some false, some true)
  have hC := outer (List.replicate u.length false ++ []) (v.reverse ++ []) []
    (none, (some false, some true).2)
  have hAB : rn ((v.length + 1) + (u.length + 1)) (cfg 0 (none, none) (pair u v) [] [] [] []) =
      some (cfg 2 (none, (some false, some true).2) [] [] (List.replicate u.length false ++ [])
        (v.reverse ++ []) []) := by
    rw [rn_add hA]
    exact hB
  have ht : rn (((List.replicate u.length false ++ []).length * (2 * (v.reverse ++ []).length + 3)
      + (v.reverse ++ []).length + 2) + ((v.length + 1) + (u.length + 1)))
      (cfg 0 (none, none) (pair u v) [] [] [] []) =
      some ⟨none, (none, none), ![[], List.replicate ((List.replicate u.length false ++ []).length *
        (v.reverse ++ []).length) false ++ [], [], [], []]⟩ := by
    rw [rn_add hAB]
    exact hC
  simpa using rn_unique hs ht

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] [] [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, (none, none), ![[], O, [], [], []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tm]

/-- The machine for unary multiplication on the pair encoding. -/
noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) mul where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X ^ 2 + 6 * Polynomial.X + 4
  outputsFun z := by
    have hs := (mul_spec z).choose_spec.1
    have he := (mul_spec z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(mul_spec z).choose]
        (some (initList tm z)) = some (haltList tm (mul z)) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(mul_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (mul z))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat, Polynomial.eval_pow]
      exact hs

theorem main : ∃ M : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) M) ∧
    ∀ u v : List Bool, M (pair u v) = List.replicate (u.length * v.length) false :=
  ⟨mul, ⟨machine⟩, mul_pair⟩

end MPP.Solutions.Pnp032
