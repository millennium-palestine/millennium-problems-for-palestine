import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp085

open Computability Turing MPP.PvsNP

/-- The state: the last symbol popped from the input (or from the accumulator), the one popped
from the output stack, and the flag `ok`, which stays `true` while all compared symbols agree. -/
abbrev St := Option Bool × Option Bool × Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 4) St

/-- Program of the equality machine. Stacks: `0` input, `1` output (used as a scratch copy of the
witness), `2` accumulator. Label 0 reads the doubled instance two symbols at a time and pushes
each bit onto the accumulator, so the accumulator holds the instance reversed. At the first
mismatch, which is the separator `[false, true]`, it goes to label 1. Label 1 moves the rest of the
input, the witness, onto stack `1`, so stack `1` holds the witness reversed. Label 2 pops stacks
`2` and `1` together, keeping `ok` false from the first difference on, and stops when both are
empty. Label 3 pushes the flag and halts. -/
def prog : Fin 4 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 4) St
  | 0 => .pop 0 (fun s h => (h, s.2.1, s.2.2))
      (.pop 0 (fun s h => (s.1, h, s.2.2))
        (.branch (fun s => decide (s.1 = s.2.1 ∧ s.1.isSome))
          (.push 2 (fun s => s.1.getD false) (.goto fun _ => 0))
          (.goto fun _ => 1)))
  | 1 => .pop 0 (fun s h => (h, s.2.1, s.2.2))
      (.branch (fun s => s.1.isSome)
        (.push 1 (fun s => s.1.getD false) (.goto fun _ => 1))
        (.goto fun _ => 2))
  | 2 => .pop 2 (fun s h => (h, s.2.1, s.2.2))
      (.pop 1 (fun s h => (s.1, h, s.2.2))
        (.branch (fun s => s.1.isNone && s.2.1.isNone)
          (.goto fun _ => 3)
          (.load (fun s => (none, none, s.2.2 && decide (s.1 = s.2.1)))
            (.goto fun _ => 2))))
  | 3 => .push 1 (fun s => s.2.2) (.load (fun _ => (none, none, true)) .halt)

/-- The equality machine: input stack `0`, output stack `1`, accumulator `2`. -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 4
  main := 0
  σ := St
  initialState := (none, none, true)
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input), `O` (output), `B`
(accumulator). -/
def cfg (l : Fin 4) (v : St) (R O B : List Bool) : Cfg :=
  ⟨some l, v, ![R, O, B]⟩

theorem step0_match (a : Bool) (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) O A) = some (cfg 0 (some a, some a, v.2.2) R O (a :: A)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_mismatch (a b : Bool) (hab : a ≠ b) (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O A) = some (cfg 1 (some a, some b, v.2.2) R O A) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem step0_one (a : Bool) (v : St) (O A : List Bool) :
    TM2.step prog (cfg 0 v [a] O A) = some (cfg 1 (some a, none, v.2.2) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step0_nil (v : St) (O A : List Bool) :
    TM2.step prog (cfg 0 v [] O A) = some (cfg 1 (none, none, v.2.2) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_push (a : Bool) (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 1 v (a :: R) O A) = some (cfg 1 (some a, v.2.1, v.2.2) R (a :: O) A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step1_end (v : St) (O A : List Bool) :
    TM2.step prog (cfg 1 v [] O A) = some (cfg 2 (none, v.2.1, v.2.2) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_both (a b : Bool) (v : St) (B A : List Bool) :
    TM2.step prog (cfg 2 v [] (b :: B) (a :: A)) =
      some (cfg 2 (none, none, v.2.2 && decide (some a = some b)) [] B A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_left (a : Bool) (v : St) (A : List Bool) :
    TM2.step prog (cfg 2 v [] [] (a :: A)) =
      some (cfg 2 (none, none, v.2.2 && decide (some a = none)) [] [] A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_right (b : Bool) (v : St) (B : List Bool) :
    TM2.step prog (cfg 2 v [] (b :: B) []) =
      some (cfg 2 (none, none, v.2.2 && decide (none = some b)) [] B []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step2_end (v : St) :
    TM2.step prog (cfg 2 v [] [] []) = some (cfg 3 (none, none, v.2.2) [] [] []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem step3 (v : St) :
    TM2.step prog (cfg 3 v [] [] []) = some ⟨none, (none, none, true), ![[], [v.2.2], []]⟩ := by
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

theorem rn_halt (t : ℕ) (H : Cfg) (hH : H.l = none) : rn (t + 1) H = none := by
  unfold rn
  rw [Function.iterate_succ_apply]
  have hs : TM2.step prog H = none := by
    obtain ⟨l, v, S⟩ := H
    simp only at hH
    subst hH
    rfl
  simp only [Option.bind_some, hs]
  exact Function.iterate_fixed rfl t

theorem rn_halted {H K : Cfg} {d : ℕ} (hH : H.l = none) (h : rn d H = some K) : d = 0 ∧ H = K := by
  cases d with
  | zero =>
    simp only [rn, Function.iterate_zero, id_eq, Option.some.injEq] at h
    exact ⟨rfl, h⟩
  | succ d =>
    rw [rn_halt d H hH] at h
    cases h

theorem rn_unique {c : Cfg} {s t : ℕ} {O P : List Bool}
    (hs : rn s c = some ⟨none, (none, none, true), ![[], O, []]⟩)
    (ht : rn t c = some ⟨none, (none, none, true), ![[], P, []]⟩) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : Cfg => H.stk 1) hK
    simpa using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : Cfg => H.stk 1) hK
    simpa using this.symm

/-- Phase 0: the instance bits are pushed onto the accumulator, reversed, and the separator is
consumed. -/
theorem phase0 (x w O A : List Bool) (v : St) :
    rn (x.length + 1) (cfg 0 v (MPP.PvsNP.pair x w) O A) =
      some (cfg 1 (some false, some true, v.2.2) w O (x.reverse ++ A)) := by
  induction x generalizing A v with
  | nil =>
    have hp : MPP.PvsNP.pair [] w = false :: true :: w := by simp [MPP.PvsNP.pair]
    rw [hp, show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_mismatch false true (by decide) v w O A)]
    simp [rn]
  | cons a x ih =>
    have hp : MPP.PvsNP.pair (a :: x) w = a :: a :: MPP.PvsNP.pair x w := by
      simp [MPP.PvsNP.pair, List.flatMap_cons]
    rw [hp, rn_succ_step (step0_match a v (MPP.PvsNP.pair x w) O A)]
    rw [show (a :: x).length = x.length + 1 from rfl]
    rw [ih (a :: A) (some a, some a, v.2.2)]
    simp [List.reverse_cons, List.append_assoc]

/-- Phase 1: the rest of the input is copied onto the output stack, reversed. -/
theorem copyW (R O A : List Bool) (v : St) :
    rn (R.length + 1) (cfg 1 v R O A) = some (cfg 2 (none, v.2.1, v.2.2) [] (R.reverse ++ O) A) := by
  induction R generalizing O v with
  | nil =>
    rw [rn_succ_step (step1_end v O A)]
    simp [rn]
  | cons a R ih =>
    rw [show (a :: R).length = R.length + 1 from rfl]
    rw [rn_succ_step (step1_push a v R O A)]
    rw [ih (a :: O) (some a, v.2.1, v.2.2)]
    simp [List.reverse_cons, List.append_assoc]

/-- Phase 2: the two stacks are compared, popping both at each step. -/
theorem cmpRun : ∀ (m : ℕ) (A B : List Bool) (v : St), max A.length B.length = m →
    rn (m + 1) (cfg 2 v [] B A) = some (cfg 3 (none, none, v.2.2 && decide (A = B)) [] [] [])
  | 0, A, B, v, hm => by
    have hA : A = [] := by
      cases A with
      | nil => rfl
      | cons a A => simp at hm
    have hB : B = [] := by
      cases B with
      | nil => rfl
      | cons b B => simp at hm
    subst hA
    subst hB
    rw [show (0 : ℕ) + 1 = 0 + 1 from rfl, rn_succ_step (step2_end v)]
    simp [rn]
  | m + 1, A, B, v, hm => by
    cases A with
    | nil =>
      cases B with
      | nil => simp at hm
      | cons b B =>
        rw [rn_succ_step (step2_right b v B)]
        have hm' : max ([] : List Bool).length B.length = m := by simp at hm ⊢; omega
        rw [cmpRun m [] B _ hm']
        congr 2
        simp
    | cons a A =>
      cases B with
      | nil =>
        rw [rn_succ_step (step2_left a v A)]
        have hm' : max A.length ([] : List Bool).length = m := by simp at hm ⊢; omega
        rw [cmpRun m A [] _ hm']
        congr 2
        simp
      | cons b B =>
        rw [rn_succ_step (step2_both a b v B A)]
        have hm' : max A.length B.length = m := by simp at hm ⊢; omega
        rw [cmpRun m A B _ hm']
        congr 2
        by_cases hab : a = b <;> by_cases hAB : A = B <;> simp [hab, hAB]

theorem halt3 (v : St) : rn 1 (cfg 3 v [] [] []) = some ⟨none, (none, none, true), ![[], [v.2.2], []]⟩ := by
  show rn (0 + 1) (cfg 3 v [] [] []) = _
  rw [rn_succ_step (step3 v)]
  simp [rn]

/-- For any input, phase 0 halts after at most `|R| + 1` steps. -/
theorem phase0_gen : ∀ (R A : List Bool) (v : St),
    ∃ s, s ≤ R.length + 1 ∧ ∃ (p q : Option Bool) (R' A' : List Bool),
      rn s (cfg 0 v R [] A) = some (cfg 1 (p, q, v.2.2) R' [] A') ∧
        R'.length + A'.length ≤ R.length + A.length
  | [], A, v => ⟨1, by simp, none, none, [], A, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_nil v [] A)]; simp [rn], by simp⟩
  | [a], A, v => ⟨1, by simp, some a, none, [], A, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_one a v [] A)]; simp [rn], by simp⟩
  | a :: b :: R, A, v => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨s, hs, p, q, R', A', h, hl⟩ := phase0_gen R (a :: A) (some a, some a, v.2.2)
      refine ⟨s + 1, by simp only [List.length_cons]; omega, p, q, R', A', ?_, by
        simp only [List.length_cons] at hl ⊢; omega⟩
      rw [rn_succ_step (step0_match a v R [] A)]
      exact h
    · exact ⟨1, by simp, some a, some b, R, A, by
        rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (step0_mismatch a b hab v R [] A)]
        simp [rn], by simp only [List.length_cons]; omega⟩

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none, true) z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) :
    haltList tm O = ⟨none, (none, none, true), ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

/-- Every input is processed in at most `3|z| + 5` steps, to a single output bit. -/
theorem gen (z : List Bool) : ∃ b : Bool, ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none, true) z [] []) = some ⟨none, (none, none, true), ![[], [b], []]⟩ := by
  obtain ⟨s1, hs1, p, q, R', A', h1, hl⟩ := phase0_gen z [] (none, none, true)
  have h2 := copyW R' [] A' (p, q, true)
  have h3 := cmpRun (max A'.length (R'.reverse ++ []).length) A' (R'.reverse ++ [])
    (none, q, true) rfl
  have hA := (rn_add (n := R'.length + 1) h1).trans h2
  have hB := (rn_add (n := (max A'.length (R'.reverse ++ []).length) + 1) hA).trans h3
  have hC := (rn_add (n := 1) hB).trans (halt3 _)
  refine ⟨_, _, ?_, hC⟩
  simp only [List.length_reverse, List.append_nil, List.length_nil, add_zero] at hl ⊢
  omega

/-- The output bit of the machine on an input. -/
noncomputable def eqBit (z : List Bool) : Bool := (gen z).choose

theorem eqBit_spec (z : List Bool) : ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none, true) z [] []) = some ⟨none, (none, none, true), ![[], [eqBit z], []]⟩ :=
  (gen z).choose_spec

/-- On a pair, the machine halts with the decision `decide (w = x)`. -/
theorem pair_run (x w : List Bool) : ∃ s,
    rn s (cfg 0 (none, none, true) (MPP.PvsNP.pair x w) [] []) =
      some ⟨none, (none, none, true), ![[], [decide (w = x)], []]⟩ := by
  have h1 := phase0 x w [] [] (none, none, true)
  have h2 := copyW w [] (x.reverse ++ []) (some false, some true, true)
  have h3 := cmpRun (max (x.reverse ++ []).length (w.reverse ++ []).length) (x.reverse ++ [])
    (w.reverse ++ []) (none, some true, true) rfl
  have hA := (rn_add (n := w.length + 1) h1).trans h2
  have hB := (rn_add (n := (max (x.reverse ++ []).length (w.reverse ++ []).length) + 1) hA).trans h3
  have hC := (rn_add (n := 1) hB).trans (halt3 _)
  refine ⟨_, hC.trans ?_⟩
  congr 3
  simp [List.reverse_inj, eq_comm]

theorem eqBit_pair (x w : List Bool) : eqBit (MPP.PvsNP.pair x w) = decide (w = x) := by
  obtain ⟨s1, -, h1⟩ := eqBit_spec (MPP.PvsNP.pair x w)
  obtain ⟨s2, h2⟩ := pair_run x w
  have := rn_unique h1 h2
  simpa using this

theorem halt_eq_list (b : Bool) : List.map (Equiv.refl Bool).invFun (encodeBool b) = [b] := by
  simp [encodeBool]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool eqBit where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 5
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[(eqBit_spec z).choose] (some (initList tm z)) =
        some (haltList tm [eqBit z]) := by
      rw [initList_eq, haltList_eq]
      exact (eqBit_spec z).choose_spec.2
    refine ⟨⟨(eqBit_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have := (eqBit_spec z).choose_spec.1
      omega

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = decide (w = x) :=
  ⟨eqBit, ⟨machine⟩, eqBit_pair⟩

end MPP.Solutions.Pnp085
