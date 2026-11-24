import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp028

open MPP.PvsNP Computability Turing

/-- Program of the length-comparison machine. Stacks: `0` input, `1` output, `2` spare.
The state holds the last one or two symbols read.

* Label 0 reads two input symbols. A doubled bit pushes `false` onto the spare stack and repeats;
  otherwise the separator has been read and the machine moves to label 1.
* Label 1 reads one symbol of the witness. If there is none, go to label 2; otherwise to label 3.
* Label 2 empties the spare stack, then writes `true` and halts.
* Label 3 pops one symbol of the spare stack. If there was one, go back to label 1; otherwise
  go to label 4.
* Label 4 empties the input, then writes `false` and halts. -/
def prog : Fin 5 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun s h => (h, s.2)) (.pop 0 (fun s h => (s.1, h))
      (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
        (.push 2 (fun _ => false) (.goto fun _ => 0))
        (.goto fun _ => 1)))
  | 1 => .pop 0 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.goto fun _ => 3)
        (.goto fun _ => 2))
  | 2 => .pop 2 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.goto fun _ => 2)
        (.push 1 (fun _ => true) (.load (fun _ => (none, none)) .halt)))
  | 3 => .pop 2 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => 1)
        (.goto fun _ => 4))
  | 4 => .pop 0 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.goto fun _ => 4)
        (.push 1 (fun _ => false) (.load (fun _ => (none, none)) .halt)))

/-- The length-comparison machine: stacks `0` (input), `1` (output), `2` (spare). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, input `R`, output `O` and spare stack `A`. -/
def cfg (l : Fin 5) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, A]⟩

theorem step0_match (a : Bool) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) O A) = some (cfg 0 (some a, some a) R O (false :: A)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_mismatch (a b : Bool) (hab : a ≠ b) (v : Option Bool × Option Bool)
    (R O A : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O A) = some (cfg 1 (some a, some b) R O A) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem step0_one (a : Bool) (v : Option Bool × Option Bool) (O A : List Bool) :
    TM2.step prog (cfg 0 v [a] O A) = some (cfg 1 (some a, none) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : Option Bool × Option Bool) (O A : List Bool) :
    TM2.step prog (cfg 0 v [] O A) = some (cfg 1 (none, none) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_some (a : Bool) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.step prog (cfg 1 v (a :: R) O A) = some (cfg 3 (some a, v.2) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_none (v : Option Bool × Option Bool) (O A : List Bool) :
    TM2.step prog (cfg 1 v [] O A) = some (cfg 2 (none, v.2) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_some (b : Bool) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.step prog (cfg 2 v R O (b :: A)) = some (cfg 2 (some b, v.2) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_none (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 2 v [] O []) = some ⟨none, (none, none), ![[], true :: O, []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step3_some (b : Bool) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.step prog (cfg 3 v R O (b :: A)) = some (cfg 1 (v.1, some b) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step3_none (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 3 v R O []) = some (cfg 4 (v.1, none) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step4_some (b : Bool) (v : Option Bool × Option Bool) (R O A : List Bool) :
    TM2.step prog (cfg 4 v (b :: R) O A) = some (cfg 4 (some b, v.2) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step4_none (v : Option Bool × Option Bool) (O : List Bool) :
    TM2.step prog (cfg 4 v [] O []) = some ⟨none, (none, none), ![[], false :: O, []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Phase 0 on a pair encoding: the doubled part of `u` is consumed, one `false` per doubled
pair goes onto the spare stack, and the machine stops at the separator with `w` on the input. -/
theorem phase0 (u w A : List Bool) (v : Option Bool × Option Bool) :
    rn (u.length + 1) (cfg 0 v (pair u w) [] A) =
      some (cfg 1 (some false, some true) w [] (List.replicate u.length false ++ A)) := by
  induction u generalizing A v with
  | nil =>
    have hp : pair [] w = false :: true :: w := by simp [pair]
    rw [hp, show ([] : List Bool).length + 1 = 0 + 1 from rfl,
      rn_succ_step (step0_mismatch false true (by decide) v w [] A)]
    simp [rn]
  | cons a u ih =>
    have hp : pair (a :: u) w = a :: a :: pair u w := by
      simp [pair, List.flatMap_cons]
    rw [hp, show (a :: u).length + 1 = (u.length + 1) + 1 from rfl,
      rn_succ_step (step0_match a v (pair u w) [] A)]
    rw [ih (false :: A) (some a, some a)]
    simp [List.replicate_succ', List.append_assoc]

/-- Phase 0 for an arbitrary input: it stops after at most `|z| + 1` steps, with the rest of the
input no longer than `z`, and the spare stack no longer than `A` plus `z`. -/
theorem phase0_gen : ∀ (z A : List Bool) (st : Option Bool × Option Bool),
    ∃ s, s ≤ z.length + 1 ∧ ∃ (st' : Option Bool × Option Bool) (R A' : List Bool),
      rn s (cfg 0 st z [] A) = some (cfg 1 st' R [] A') ∧
        R.length ≤ z.length ∧ A'.length ≤ A.length + z.length
  | [], A, st => ⟨1, by simp, (none, none), [], A,
      (rn_succ_step (n := 0) (step0_nil st [] A)).trans (by simp [rn]), by simp, by simp⟩
  | [a], A, st => ⟨1, by simp, (some a, none), [], A,
      (rn_succ_step (n := 0) (step0_one a st [] A)).trans (by simp [rn]), by simp, by simp⟩
  | a :: b :: R, A, st => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, hs, st', R', A', h, hl, hA⟩ := phase0_gen R (false :: A) (some a, some a)
      refine ⟨s + 1, by simp only [List.length_cons] at hs ⊢; omega, st', R', A', ?_, by
        simp only [List.length_cons] at hl ⊢; omega, by
        simp only [List.length_cons, List.length_cons] at hA ⊢; omega⟩
      rw [rn_succ_step (step0_match a st R [] A)]
      exact h
    · exact ⟨1, by simp, (some a, some b), R, A,
        (rn_succ_step (n := 0) (step0_mismatch a b hab st R [] A)).trans (by simp [rn]),
        by simp only [List.length_cons]; omega, by simp⟩

/-- Label 2 empties the spare stack, then writes `true` onto the output. -/
theorem drain2 : ∀ (A O : List Bool) (st : Option Bool × Option Bool),
    rn (A.length + 1) (cfg 2 st [] O A) = some ⟨none, (none, none), ![[], true :: O, []]⟩
  | [], O, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step2_none st O)]
    simp [rn]
  | b :: A, O, st => by
    rw [show (b :: A).length + 1 = (A.length + 1) + 1 from rfl,
      rn_succ_step (step2_some b st [] O A)]
    exact drain2 A O _

/-- Label 4 empties the input, then writes `false` onto the output. -/
theorem drain4 : ∀ (R O : List Bool) (st : Option Bool × Option Bool),
    rn (R.length + 1) (cfg 4 st R O []) = some ⟨none, (none, none), ![[], false :: O, []]⟩
  | [], O, st => by
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (step4_none st O)]
    simp [rn]
  | b :: R, O, st => by
    rw [show (b :: R).length + 1 = (R.length + 1) + 1 from rfl,
      rn_succ_step (step4_some b st R O [])]
    exact drain4 R O _

/-- Phase 2: from the witness `w` on the input, with the spare stack `A`, the machine writes
`decide (|w| ≤ |A|)` after at most `2|w| + |A| + 2` steps. -/
theorem phase2 : ∀ (w A : List Bool) (st : Option Bool × Option Bool),
    ∃ s, s ≤ 2 * w.length + A.length + 2 ∧
      rn s (cfg 1 st w [] A) =
        some ⟨none, (none, none), ![[], [decide (w.length ≤ A.length)], []]⟩
  | [], A, st => by
    refine ⟨A.length + 1 + 1, by simp, ?_⟩
    rw [rn_succ_step (n := A.length + 1) (step1_none st [] A)]
    simpa using drain2 A [] (none, st.2)
  | a :: w, [], st => by
    refine ⟨w.length + 1 + 1 + 1, by simp, ?_⟩
    rw [rn_succ_step (n := w.length + 1 + 1) (step1_some a st w [] []),
      rn_succ_step (n := w.length + 1) (step3_none _ w [])]
    simpa using drain4 w [] _
  | a :: w, b :: A, st => by
    obtain ⟨s, hs, h⟩ := phase2 w A (some a, some b)
    refine ⟨s + 1 + 1, by simp only [List.length_cons]; omega, ?_⟩
    rw [rn_succ_step (n := s + 1) (step1_some a st w [] (b :: A)),
      rn_succ_step (n := s) (step3_some b _ w [] A)]
    simpa using h

/-- Every input halts after at most `4|z| + 3` steps, with a Boolean output. -/
theorem gen (z : List Bool) : ∃ b : Bool, ∃ s, s ≤ 4 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], [b], []]⟩ := by
  obtain ⟨s1, hs1, st', R', A', h1, hR, hA⟩ := phase0_gen z [] (none, none)
  obtain ⟨s2, hs2, h2⟩ := phase2 R' A' st'
  simp only [List.length_nil, zero_add] at hA
  refine ⟨decide (R'.length ≤ A'.length), s2 + s1, by omega, ?_⟩
  rw [rn_add h1]
  exact h2

theorem rn_halted {H K : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
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

theorem rn_unique {c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
    {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none), ![[], O, []]⟩)
    (ht : rn t c = some ⟨none, (none, none), ![[], P, []]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5)
      (Option Bool × Option Bool) => H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5)
      (Option Bool × Option Bool) => H.stk 1) hK
    simpa using this.symm

/-- The machine's output on the input. -/
noncomputable def cmp (z : List Bool) : Bool := (gen z).choose

theorem cmp_spec (z : List Bool) : ∃ s, s ≤ 4 * z.length + 3 ∧
    rn s (cfg 0 (none, none) z [] []) = some ⟨none, (none, none), ![[], [cmp z], []]⟩ :=
  (gen z).choose_spec

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) : haltList tm O = ⟨none, (none, none), ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem cmp_pair (u w : List Bool) : cmp (pair u w) = decide (w.length ≤ u.length) := by
  obtain ⟨-, hs⟩ := (cmp_spec (pair u w)).choose_spec
  have h0 := phase0 u w [] (none, none)
  obtain ⟨s, -, h2⟩ := phase2 w (List.replicate u.length false ++ []) (some false, some true)
  have hB : rn (s + (u.length + 1)) (cfg 0 (none, none) (pair u w) [] []) =
      some ⟨none, (none, none), ![[], [decide (w.length ≤ u.length)], []]⟩ := by
    rw [rn_add (by simpa using h0)]
    simpa using h2
  have := rn_unique hs hB
  simpa using this

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool cmp where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 3
  outputsFun z := by
    have hs := (cmp_spec z).choose_spec.1
    have he := (cmp_spec z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(cmp_spec z).choose]
        (some (initList tm z)) = some (haltList tm (encodeBool (cmp z))) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(cmp_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (encodeBool (cmp z)))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ C : List Bool → Bool, InP C ∧
    ∀ u w : List Bool, C (pair u w) = true ↔ w.length ≤ u.length :=
  ⟨cmp, ⟨machine⟩, fun u w => by rw [cmp_pair]; simp⟩

end MPP.Solutions.Pnp028
