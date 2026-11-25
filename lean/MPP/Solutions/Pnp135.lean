import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp135

open Computability Turing MPP.PvsNP

/-- The state: the last two symbols popped, as in pnp-134. -/
abbrev St := Option Bool × Option Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 9) St

/-- Program of the indexed lookup machine. Stacks: `0` the input, and after the separator the
witness; `1` output; `2` counter marks; `3` scratch; `4` the instance bits, most significant bit on
top. The counter `c` is the value of the instance prefix read so far, kept as `c` marks on stack 2.
Label 0 reads a doubled instance bit and pushes it on stack 3, or stops at the separator (or at the
end of the input). Label 1 moves stack 3 to stack 4, which reverses it. Label 2 reads the next
instance bit: a true bit also drops one witness symbol and pushes one mark on stack 3. Label 3 doubles
the counter: each mark drops one witness symbol and pushes two marks on stack 3. Label 4 moves stack 3
back to stack 2. Label 5 takes the head of the witness into the state, label 6 discards the rest of
the witness, label 7 discards the marks, and label 8 outputs the head and halts. Witness symbols are
popped only when the stack is nonempty, so an exhausted witness just stays empty. -/
def prog : Fin 9 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 9) St
  | 0 => .pop 0 (fun s h => (h, s.2))
      (.pop 0 (fun s h => (s.1, h))
        (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
          (.push 3 (fun s => s.1.getD false) (.goto fun _ => 0))
          (.goto fun _ => 1)))
  | 1 => .pop 3 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 4 (fun s => s.1.getD false) (.goto fun _ => 1))
        (.goto fun _ => 2))
  | 2 => .pop 4 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => decide (s.1 = some true))
          (.pop 0 (fun s h => (s.1, h))
            (.branch (fun s => s.2.isSome)
              (.push 3 (fun _ => true) (.goto fun _ => 3))
              (.goto fun _ => 3)))
          (.goto fun _ => 3))
        (.goto fun _ => 5))
  | 3 => .pop 2 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.pop 0 (fun s h => (s.1, h))
          (.branch (fun s => s.2.isSome)
            (.push 3 (fun _ => true) (.push 3 (fun _ => true) (.goto fun _ => 3)))
            (.goto fun _ => 3)))
        (.goto fun _ => 4))
  | 4 => .pop 3 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome)
        (.push 2 (fun _ => true) (.goto fun _ => 4))
        (.goto fun _ => 2))
  | 5 => .pop 0 (fun s h => (h, s.2)) (.goto fun _ => 6)
  | 6 => .pop 0 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome) (.goto fun _ => 6) (.goto fun _ => 7))
  | 7 => .pop 2 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome) (.goto fun _ => 7) (.goto fun _ => 8))
  | 8 => .push 1 (fun s => s.1.getD false) (.load (fun _ => (none, none)) .halt)

/-- The lookup machine: input stack `0`, output stack `1`. -/
def tm : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 9
  main := 0
  σ := St
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input), `O` (output), `M` (marks),
`T` (scratch), `B` (instance bits). -/
def cfg (l : Fin 9) (v : St) (R O M T B : List Bool) : Cfg :=
  ⟨some l, v, ![R, O, M, T, B]⟩

/-- The halting configuration with output stack `O`. -/
def hcfg (O : List Bool) : Cfg :=
  ⟨none, (none, none), ![[], O, [], [], []]⟩

/-- The instance bits (most significant first) and the witness, read by label 0. -/
def splitZ : List Bool → List Bool × List Bool
  | [] => ([], [])
  | [_] => ([], [])
  | a :: b :: R => if a = b then (a :: (splitZ R).1, (splitZ R).2) else ([], R)

/-- The lookup bit of an input. -/
def lookupBit (z : List Bool) : Bool :=
  (splitZ z).2.getD ((splitZ z).1.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0) false

theorem st0_eq (a : Bool) (v : St) (R O M T B : List Bool) :
    TM2.step prog (cfg 0 v (a :: a :: R) O M T B) =
      some (cfg 0 (some a, some a) R O M (a :: T) B) := by
  cases a <;> simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st0_ne (a b : Bool) (hab : a ≠ b) (v : St) (R O M T B : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O M T B) =
      some (cfg 1 (some a, some b) R O M T B) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem st0_one (a : Bool) (v : St) (O M T B : List Bool) :
    TM2.step prog (cfg 0 v [a] O M T B) = some (cfg 1 (some a, none) [] O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st0_nil (v : St) (O M T B : List Bool) :
    TM2.step prog (cfg 0 v [] O M T B) = some (cfg 1 (none, none) [] O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st1_cons (a : Bool) (v : St) (R O M T B : List Bool) :
    TM2.step prog (cfg 1 v R O M (a :: T) B) =
      some (cfg 1 (some a, v.2) R O M T (a :: B)) := by
  cases a <;> simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st1_nil (v : St) (R O M B : List Bool) :
    TM2.step prog (cfg 1 v R O M [] B) = some (cfg 2 (none, v.2) R O M [] B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_end (v : St) (R O M : List Bool) :
    TM2.step prog (cfg 2 v R O M [] []) = some (cfg 5 (none, v.2) R O M [] []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_zero (v : St) (R O M B : List Bool) :
    TM2.step prog (cfg 2 v R O M [] (false :: B)) =
      some (cfg 3 (some false, v.2) R O M [] B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_one_cons (v : St) (a : Bool) (R O M B : List Bool) :
    TM2.step prog (cfg 2 v (a :: R) O M [] (true :: B)) =
      some (cfg 3 (some true, some a) R O M [true] B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_one_nil (v : St) (O M B : List Bool) :
    TM2.step prog (cfg 2 v [] O M [] (true :: B)) =
      some (cfg 3 (some true, none) [] O M [] B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st3_none (v : St) (R O T B : List Bool) :
    TM2.step prog (cfg 3 v R O [] T B) = some (cfg 4 (none, v.2) R O [] T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st3_cons (v : St) (a : Bool) (R O M T B : List Bool) :
    TM2.step prog (cfg 3 v (a :: R) O (true :: M) T B) =
      some (cfg 3 (some true, some a) R O M (true :: true :: T) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st3_nil (v : St) (O M T B : List Bool) :
    TM2.step prog (cfg 3 v [] O (true :: M) T B) =
      some (cfg 3 (some true, none) [] O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st4_cons (v : St) (R O M T B : List Bool) :
    TM2.step prog (cfg 4 v R O M (true :: T) B) =
      some (cfg 4 (some true, v.2) R O (true :: M) T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st4_nil (v : St) (R O M B : List Bool) :
    TM2.step prog (cfg 4 v R O M [] B) = some (cfg 2 (none, v.2) R O M [] B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st5_cons (v : St) (a : Bool) (R O M T B : List Bool) :
    TM2.step prog (cfg 5 v (a :: R) O M T B) = some (cfg 6 (some a, v.2) R O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st5_nil (v : St) (O M T B : List Bool) :
    TM2.step prog (cfg 5 v [] O M T B) = some (cfg 6 (none, v.2) [] O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st6_cons (v : St) (a : Bool) (R O M T B : List Bool) :
    TM2.step prog (cfg 6 v (a :: R) O M T B) = some (cfg 6 (v.1, some a) R O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st6_nil (v : St) (O M T B : List Bool) :
    TM2.step prog (cfg 6 v [] O M T B) = some (cfg 7 (v.1, none) [] O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st7_cons (v : St) (a : Bool) (R O M T B : List Bool) :
    TM2.step prog (cfg 7 v R O (a :: M) T B) = some (cfg 7 (v.1, some a) R O M T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st7_nil (v : St) (R O T B : List Bool) :
    TM2.step prog (cfg 7 v R O [] T B) = some (cfg 8 (v.1, none) R O [] T B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st8 (v : St) (O : List Bool) :
    TM2.step prog (cfg 8 v [] O [] [] []) = some (hcfg (v.1.getD false :: O)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg, hcfg] <;> (funext k; fin_cases k <;> simp)

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

theorem rn_trans {m n : ℕ} {c c' c'' : Cfg} (h1 : rn m c = some c') (h2 : rn n c' = some c'') :
    rn (m + n) c = some c'' := by
  rw [Nat.add_comm]
  exact (rn_add (n := n) h1).trans h2

/-- Label 6 discards the witness: one step per symbol, then one step to label 7. -/
theorem drain0 : ∀ (L : List Bool) (v : St) (O M T B : List Bool),
    rn (L.length + 1) (cfg 6 v L O M T B) = some (cfg 7 (v.1, none) [] O M T B)
  | [], v, O, M, T, B => by
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st6_nil v O M T B)]
    simp [rn]
  | a :: L, v, O, M, T, B => by
    show rn (L.length + 1 + 1) _ = _
    rw [rn_succ_step (st6_cons v a L O M T B)]
    exact drain0 L (v.1, some a) O M T B

/-- Label 7 discards the marks: one step per mark, then one step to label 8. -/
theorem drain2 : ∀ (M : List Bool) (v : St) (R O T B : List Bool),
    rn (M.length + 1) (cfg 7 v R O M T B) = some (cfg 8 (v.1, none) R O [] T B)
  | [], v, R, O, T, B => by
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st7_nil v R O T B)]
    simp [rn]
  | a :: M, v, R, O, T, B => by
    show rn (M.length + 1 + 1) _ = _
    rw [rn_succ_step (st7_cons v a R O M T B)]
    exact drain2 M (v.1, some a) R O T B

theorem rep_two (x : ℕ) (T : List Bool) :
    List.replicate (x + 1 + 1) true ++ T = List.replicate x true ++ true :: true :: T := by
  rw [show x + 1 + 1 = x + 2 from rfl, List.replicate_add, List.append_assoc]
  rfl

theorem rep_cons (n : ℕ) (M : List Bool) :
    List.replicate n true ++ true :: M = true :: (List.replicate n true ++ M) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Phase 0: each doubled instance bit is one step and is pushed on stack 3; the separator, or
the end of the input, is one step to label 1. -/
theorem ph0 : ∀ (z : List Bool) (v : St) (O M T B : List Bool),
    ∃ v' : St, rn ((splitZ z).1.length + 1) (cfg 0 v z O M T B) =
      some (cfg 1 v' (splitZ z).2 O M ((splitZ z).1.reverse ++ T) B)
  | [], v, O, M, T, B => by
    refine ⟨(none, none), ?_⟩
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st0_nil v O M T B)]
    simp [rn, splitZ]
  | [a], v, O, M, T, B => by
    refine ⟨(some a, none), ?_⟩
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st0_one a v O M T B)]
    simp [rn, splitZ]
  | a :: b :: R, v, O, M, T, B => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨v', h⟩ := ph0 R (some a, some a) O M (a :: T) B
      refine ⟨v', ?_⟩
      have e : (splitZ (a :: a :: R)).1.length + 1 = ((splitZ R).1.length + 1) + 1 := by
        simp [splitZ]
      rw [e, rn_succ_step (st0_eq a v R O M T B), h]
      simp [splitZ]
    · refine ⟨(some a, some b), ?_⟩
      have e : (splitZ (a :: b :: R)).1.length + 1 = 0 + 1 := by
        simp [splitZ, hab]
      rw [e, rn_succ_step (st0_ne a b hab v R O M T B)]
      simp [rn, splitZ, hab]

/-- Phase 1: label 1 moves stack 3 to stack 4 one symbol per step, which reverses it. -/
theorem ph1 : ∀ (L : List Bool) (v : St) (R O M B : List Bool),
    ∃ v' : St, rn (L.length + 1) (cfg 1 v R O M L B) = some (cfg 2 v' R O M [] (L.reverse ++ B))
  | [], v, R, O, M, B => by
    refine ⟨(none, v.2), ?_⟩
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st1_nil v R O M B)]
    simp [rn]
  | a :: L, v, R, O, M, B => by
    obtain ⟨v', h⟩ := ph1 L (some a, v.2) R O M (a :: B)
    refine ⟨v', ?_⟩
    show rn (L.length + 1 + 1) _ = _
    rw [rn_succ_step (st1_cons a v R O M L B), h]
    simp [List.reverse_cons, List.append_assoc]

/-- Label 3 doubles the counter: one step per mark, then one step to label 4. -/
theorem dblLoop : ∀ (m : ℕ) (v : St) (R O T B : List Bool),
    ∃ v' : St, rn (m + 1) (cfg 3 v R O (List.replicate m true) T B) =
      some (cfg 4 v' (R.drop m) O [] (List.replicate (2 * min m R.length) true ++ T) B)
  | 0, v, R, O, T, B => by
    refine ⟨(none, v.2), ?_⟩
    show rn (0 + 1) (cfg 3 v R O [] T B) = _
    rw [rn_succ_step (st3_none v R O T B)]
    simp [rn]
  | m + 1, v, R, O, T, B => by
    rw [List.replicate_succ]
    cases R with
    | nil =>
      obtain ⟨v', h⟩ := dblLoop m (some true, none) [] O T B
      refine ⟨v', ?_⟩
      show rn (m + 1 + 1) _ = _
      rw [rn_succ_step (st3_nil v O (List.replicate m true) T B), h]
      simp
    | cons a R0 =>
      obtain ⟨v', h⟩ := dblLoop m (some true, some a) R0 O (true :: true :: T) B
      refine ⟨v', ?_⟩
      show rn (m + 1 + 1) _ = _
      rw [rn_succ_step (st3_cons v a R0 O (List.replicate m true) T B), h]
      have e : 2 * min (m + 1) (R0.length + 1) = 2 * min m R0.length + 1 + 1 := by
        have : min (m + 1) (R0.length + 1) = min m R0.length + 1 := by omega
        omega
      simp only [List.length_cons, List.drop_succ_cons]
      rw [e, rep_two]

/-- Label 4 moves stack 3 back to stack 2, one mark per step. -/
theorem mvLoop : ∀ (n : ℕ) (v : St) (R O M B : List Bool),
    ∃ v' : St, rn (n + 1) (cfg 4 v R O M (List.replicate n true) B) =
      some (cfg 2 v' R O (List.replicate n true ++ M) [] B)
  | 0, v, R, O, M, B => by
    refine ⟨(none, v.2), ?_⟩
    show rn (0 + 1) (cfg 4 v R O M [] B) = _
    rw [rn_succ_step (st4_nil v R O M B)]
    simp [rn]
  | n + 1, v, R, O, M, B => by
    obtain ⟨v', h⟩ := mvLoop n (some true, v.2) R O (true :: M) B
    refine ⟨v', ?_⟩
    rw [List.replicate_succ]
    show rn (n + 1 + 1) _ = _
    rw [rn_succ_step (st4_cons v R O M (List.replicate n true) B), h, rep_cons, List.cons_append]

/-- One Horner step on a bit of the instance: the counter `c` (as `k` marks) becomes `2 c + b`.
The witness drops `c + b` symbols, and the number of new marks is at most `2 |R| + 1`. -/
theorem bitStep (k : ℕ) (b : Bool) (B : List Bool) (v : St) (R O : List Bool) :
    ∃ k' : ℕ, ∃ v' : St, k' ≤ 2 * R.length + 1 ∧
      (R.drop (k + (if b then 1 else 0)) ≠ [] → k' = 2 * k + (if b then 1 else 0)) ∧
      rn (k + k' + 3) (cfg 2 v R O (List.replicate k true) [] (b :: B)) =
        some (cfg 2 v' (R.drop (k + (if b then 1 else 0))) O (List.replicate k' true) [] B) := by
  cases b with
  | false =>
    have h0 : rn 1 (cfg 2 v R O (List.replicate k true) [] (false :: B)) =
        some (cfg 3 (some false, v.2) R O (List.replicate k true) [] B) := by
      show rn (0 + 1) _ = _
      rw [rn_succ_step (st2_zero v R O (List.replicate k true) B)]
      simp [rn]
    obtain ⟨v1, h1⟩ := dblLoop k (some false, v.2) R O [] B
    rw [List.append_nil] at h1
    obtain ⟨v2, h2⟩ := mvLoop (2 * min k R.length) v1 (R.drop k) O [] B
    rw [List.append_nil] at h2
    refine ⟨2 * min k R.length, v2, ?_, ?_, ?_⟩
    · have := Nat.min_le_right k R.length
      omega
    · intro hne
      have hlt : k < R.length := by
        have : R.drop k ≠ [] := by simpa using hne
        rw [← List.length_pos_iff] at this
        rw [List.length_drop] at this
        omega
      have hm : min k R.length = k := Nat.min_eq_left hlt.le
      simp [hm]
    · have e : k + 2 * min k R.length + 3 = 1 + ((k + 1) + (2 * min k R.length + 1)) := by
        omega
      rw [e, rn_trans h0 (rn_trans h1 h2)]
      simp
  | true =>
    cases R with
    | nil =>
      have h0 : rn 1 (cfg 2 v [] O (List.replicate k true) [] (true :: B)) =
          some (cfg 3 (some true, none) [] O (List.replicate k true) [] B) := by
        show rn (0 + 1) _ = _
        rw [rn_succ_step (st2_one_nil v O (List.replicate k true) B)]
        simp [rn]
      obtain ⟨v1, h1⟩ := dblLoop k (some true, none) [] O [] B
      rw [List.append_nil] at h1
      obtain ⟨v2, h2⟩ := mvLoop (2 * min k ([] : List Bool).length) v1
        (([] : List Bool).drop k) O [] B
      rw [List.append_nil] at h2
      refine ⟨2 * min k ([] : List Bool).length, v2, by simp, ?_, ?_⟩
      · intro h
        simp at h
      · have e : k + 2 * min k ([] : List Bool).length + 3 =
            1 + ((k + 1) + (2 * min k ([] : List Bool).length + 1)) := by
          omega
        rw [e, rn_trans h0 (rn_trans h1 h2)]
        simp
    | cons a R0 =>
      have h0 : rn 1 (cfg 2 v (a :: R0) O (List.replicate k true) [] (true :: B)) =
          some (cfg 3 (some true, some a) R0 O (List.replicate k true) [true] B) := by
        show rn (0 + 1) _ = _
        rw [rn_succ_step (st2_one_cons v a R0 O (List.replicate k true) B)]
        simp [rn]
      obtain ⟨v1, h1⟩ := dblLoop k (some true, some a) R0 O [true] B
      rw [← List.replicate_succ'] at h1
      obtain ⟨v2, h2⟩ := mvLoop (2 * min k R0.length + 1) v1 (R0.drop k) O [] B
      rw [List.append_nil] at h2
      refine ⟨2 * min k R0.length + 1, v2, ?_, ?_, ?_⟩
      · have := Nat.min_le_right k R0.length
        simp only [List.length_cons]
        omega
      · intro hne
        have hne' : R0.drop k ≠ [] := by simpa using hne
        have hlt : k < R0.length := by
          rw [← List.length_pos_iff] at hne'
          rw [List.length_drop] at hne'
          omega
        have hm : min k R0.length = k := Nat.min_eq_left hlt.le
        simp [hm]
      · have e : k + (2 * min k R0.length + 1) + 3 =
            1 + ((k + 1) + ((2 * min k R0.length + 1) + 1)) := by
          omega
        rw [e, rn_trans h0 (rn_trans h1 h2)]
        simp

/-- The Horner loop over the instance bits (most significant first). The witness `W` after `c`
symbols dropped is the stack 0 content, as long as the counter `c` is `k` marks (whenever the
witness is not exhausted). -/
theorem hornerLoop (W : List Bool) (n : ℕ) (hW : W.length ≤ n) :
    ∀ (B : List Bool) (c k : ℕ) (R : List Bool) (v : St) (O : List Bool),
      R = W.drop c → (R ≠ [] → k = c) → k ≤ 2 * n + 1 →
      ∃ s, s ≤ B.length * (4 * n + 5) + 1 ∧ ∃ (v' : St) (M' : List Bool), M'.length ≤ 2 * n + 1 ∧
        rn s (cfg 2 v R O (List.replicate k true) [] B) =
          some (cfg 5 v' (W.drop (B.foldl (fun c b => 2 * c + (if b then 1 else 0)) c)) O M' [] [])
  | [], c, k, R, v, O, hR, _, hk2 => by
    subst hR
    refine ⟨0 + 1, by simp, (none, v.2), List.replicate k true, by simp; omega, ?_⟩
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st2_end v (W.drop c) O (List.replicate k true))]
    simp [rn]
  | b :: B', c, k, R, v, O, hR, hk, hk2 => by
    obtain ⟨k', v1, hk'le, hk'eq, hrun⟩ := bitStep k b B' v R O
    have hRlen : R.length ≤ n := by
      rw [hR, List.length_drop]
      omega
    have hstate : R.drop (k + (if b then 1 else 0)) =
        W.drop (2 * c + (if b then 1 else 0)) := by
      by_cases hRe : R = []
      · have hWc : W.length ≤ c := by
          have h' : W.drop c = [] := by rw [← hR]; exact hRe
          simpa using h'
        rw [hRe, List.drop_nil]
        exact (List.drop_eq_nil_of_le (by omega)).symm
      · have hkc := hk hRe
        subst hkc
        rw [hR, List.drop_drop]
        congr 1
        omega
    have hk'eq' : R.drop (k + (if b then 1 else 0)) ≠ [] →
        k' = 2 * c + (if b then 1 else 0) := by
      intro hne
      have hR_ne : R ≠ [] := by
        intro h
        apply hne
        rw [h]
        simp
      rw [hk'eq hne, hk hR_ne]
    obtain ⟨s', hs', v', M', hM', hrun'⟩ :=
      hornerLoop W n hW B' (2 * c + (if b then 1 else 0)) k' (R.drop (k + (if b then 1 else 0)))
        v1 O hstate hk'eq' (by omega)
    refine ⟨(k + k' + 3) + s', ?_, v', M', hM', ?_⟩
    · have e : (B'.length + 1) * (4 * n + 5) = B'.length * (4 * n + 5) + (4 * n + 5) := by
        ring
      simp only [List.length_cons]
      rw [e]
      omega
    · rw [List.foldl_cons]
      exact rn_trans hrun hrun'

/-- The final stage: the head of the witness is the answer (false when it is exhausted). Labels 5,
6, 7 and 8 discard the rest of the witness and the marks, then output. -/
theorem finStage (R O M : List Bool) (v : St) :
    ∃ s, s ≤ R.length + M.length + 4 ∧
      rn s (cfg 5 v R O M [] []) = some (hcfg ((R.head?.getD false) :: O)) := by
  cases R with
  | nil =>
    have h1 : rn (0 + 1) (cfg 5 v [] O M [] []) = some (cfg 6 (none, v.2) [] O M [] []) := by
      rw [rn_succ_step (st5_nil v O M [] [])]
      simp [rn]
    have h2 := drain0 [] (none, v.2) O M [] []
    have h3 := drain2 M (none, none) [] O [] []
    have h4 : rn (0 + 1) (cfg 8 (none, none) [] O [] [] []) =
        some (hcfg ((none : Option Bool).getD false :: O)) := by
      rw [rn_succ_step (st8 (none, none) O)]
      simp [rn]
    exact ⟨1 + (([] : List Bool).length + 1 + (M.length + 1 + (0 + 1))),
      (by simp only [List.length_nil]; omega),
      rn_trans h1 (rn_trans h2 (rn_trans h3 h4))⟩
  | cons a R0 =>
    have h1 : rn (0 + 1) (cfg 5 v (a :: R0) O M [] []) = some (cfg 6 (some a, v.2) R0 O M [] []) := by
      rw [rn_succ_step (st5_cons v a R0 O M [] [])]
      simp [rn]
    have h2 := drain0 R0 (some a, v.2) O M [] []
    have h3 := drain2 M (some a, none) [] O [] []
    have h4 : rn (0 + 1) (cfg 8 (some a, none) [] O [] [] []) =
        some (hcfg ((some a).getD false :: O)) := by
      rw [rn_succ_step (st8 (some a, none) O)]
      simp [rn]
    refine ⟨1 + (R0.length + 1 + (M.length + 1 + (0 + 1))), ?_,
      rn_trans h1 (rn_trans h2 (rn_trans h3 h4))⟩
    simp only [List.length_cons]
    omega

theorem head_drop_getD (w : List Bool) (c : ℕ) :
    (w.drop c).head?.getD false = w.getD c false := by
  simp [List.head?_drop, List.getD_eq_getElem?_getD]

theorem splitZ_pair (x w : List Bool) : splitZ (MPP.PvsNP.pair x w) = (x, w) := by
  induction x with
  | nil => simp [MPP.PvsNP.pair, splitZ]
  | cons a x ih =>
    have hp : MPP.PvsNP.pair (a :: x) w = a :: a :: MPP.PvsNP.pair x w := by
      simp [MPP.PvsNP.pair, List.flatMap_cons]
    rw [hp]
    simp [splitZ, ih]

theorem splitZ_len : ∀ z : List Bool, 2 * (splitZ z).1.length + (splitZ z).2.length ≤ z.length
  | [] => by simp [splitZ]
  | [a] => by simp [splitZ]
  | a :: b :: R => by
    by_cases hab : a = b
    · subst hab
      have ih := splitZ_len R
      simp [splitZ]
      omega
    · simp [splitZ, hab] <;> omega

/-- The whole run on an input `z`, with at most `4|z|^2 + 10|z| + 8` steps. -/
theorem runAll (z : List Bool) : ∃ s, s ≤ 4 * z.length ^ 2 + 10 * z.length + 8 ∧
    rn s (cfg 0 (none, none) z [] [] [] []) = some (hcfg [lookupBit z]) := by
  obtain ⟨v1, h0⟩ := ph0 z (none, none) [] [] [] []
  rw [List.append_nil] at h0
  obtain ⟨v2, h1⟩ := ph1 (splitZ z).1.reverse v1 (splitZ z).2 [] [] []
  rw [List.reverse_reverse, List.append_nil] at h1
  have hsz := splitZ_len z
  have hW : (splitZ z).2.length ≤ z.length := by omega
  have hB : (splitZ z).1.length ≤ z.length := by omega
  obtain ⟨s2, hs2, v3, M3, hM3, h2⟩ :=
    hornerLoop (splitZ z).2 z.length hW (splitZ z).1 0 0 (splitZ z).2 v2 []
      (by simp) (fun _ => rfl) (by omega)
  obtain ⟨s3, hs3, h3⟩ := finStage ((splitZ z).2.drop
    ((splitZ z).1.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0)) [] M3 v3
  have hl : ((splitZ z).2.drop
      ((splitZ z).1.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0)).head?.getD false
      = lookupBit z := by
    unfold lookupBit
    exact head_drop_getD _ _
  have hdrop : ((splitZ z).2.drop
      ((splitZ z).1.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0)).length ≤ z.length := by
    rw [List.length_drop]
    omega
  have hprod : (splitZ z).1.length * (4 * z.length + 5) ≤ z.length * (4 * z.length + 5) :=
    Nat.mul_le_mul_right _ hB
  have hQ : z.length * (4 * z.length + 5) = 4 * z.length ^ 2 + 5 * z.length := by ring
  refine ⟨((splitZ z).1.length + 1) + ((splitZ z).1.reverse.length + 1) + s2 + s3, ?_, ?_⟩
  · rw [List.length_reverse]
    nlinarith
  · have hrun := rn_trans (rn_trans (rn_trans h0 h1) h2) h3
    rw [hl] at hrun
    exact hrun

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] [] [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) : haltList tm O = hcfg O := by
  unfold haltList hcfg
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool lookupBit where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X ^ 2 + 10 * Polynomial.X + 8
  outputsFun z := by
    have hz := (runAll z).choose_spec
    have key : (fun o => o.bind (TM2.step prog))^[(runAll z).choose] (some (initList tm z)) =
        some (haltList tm [lookupBit z]) := by
      rw [initList_eq, haltList_eq]
      exact hz.2
    refine ⟨⟨(runAll z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_pow, Polynomial.eval_ofNat]
      exact hz.1

theorem lookupBit_pair (x w : List Bool) :
    lookupBit (MPP.PvsNP.pair x w) =
      w.getD (x.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0) false := by
  simp [lookupBit, splitZ_pair]

theorem main : ∃ L : Lang, InP L ∧
    ∀ x w : List Bool, L (MPP.PvsNP.pair x w) =
      w.getD (x.foldl (fun c b => 2 * c + (if b then 1 else 0)) 0) false :=
  ⟨lookupBit, ⟨machine⟩, lookupBit_pair⟩

end MPP.Solutions.Pnp135
