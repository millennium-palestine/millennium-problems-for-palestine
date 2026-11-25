import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp134

open Computability Turing MPP.PvsNP

/-- The state: the last symbol popped from a stack, and the one popped before it. -/
abbrev St := Option Bool × Option Bool

abbrev Cfg := TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 6) St

/-- Program of the lookup machine. Stacks: `0` input, `1` output, `2` accumulator, which holds one
mark `true` for each true bit of the instance. Label 0 reads two input symbols. Equal symbols are a
doubled instance bit: a true bit pushes a mark, and the label repeats. A mismatch is the separator
`[false, true]`, and goes to label 1. Label 1 pops the accumulator: a mark goes to label 2, which
discards one input symbol and returns to label 1, so each mark drops one witness symbol. An empty
accumulator goes to label 3. Label 3 pops the first remaining witness symbol into the state, and
label 4 discards the rest of the witness. Label 5 pushes the symbol, false if the witness is
exhausted, and halts. -/
def prog : Fin 6 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 6) St
  | 0 => .pop 0 (fun s h => (h, s.2))
      (.pop 0 (fun s h => (s.1, h))
        (.branch (fun s => decide (s.1 = s.2 ∧ s.1.isSome))
          (.branch (fun s => decide (s.1 = some true))
            (.push 2 (fun _ => true) (.goto fun _ => 0))
            (.goto fun _ => 0))
          (.goto fun _ => 1)))
  | 1 => .pop 2 (fun s h => (h, s.2))
      (.branch (fun s => s.1.isSome) (.goto fun _ => 2) (.goto fun _ => 3))
  | 2 => .pop 0 (fun s _ => s) (.goto fun _ => 1)
  | 3 => .pop 0 (fun s h => (h, s.2)) (.goto fun _ => 4)
  | 4 => .pop 0 (fun s h => (s.1, h))
      (.branch (fun s => s.2.isSome) (.goto fun _ => 4) (.goto fun _ => 5))
  | 5 => .push 1 (fun s => s.1.getD false) (.load (fun _ => (none, none)) .halt)

/-- The lookup machine: input stack `0`, output stack `1`, accumulator `2`. -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 6
  main := 0
  σ := St
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, and stacks `R` (input), `O` (output), `A`
(accumulator). -/
def cfg (l : Fin 6) (v : St) (R O A : List Bool) : Cfg :=
  ⟨some l, v, ![R, O, A]⟩

/-- The halting configuration with output stack `O`. -/
def hcfg (O : List Bool) : Cfg :=
  ⟨none, (none, none), ![[], O, []]⟩

theorem st0_TT (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (true :: true :: R) O A) =
      some (cfg 0 (some true, some true) R O (true :: A)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st0_FF (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (false :: false :: R) O A) =
      some (cfg 0 (some false, some false) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st0_mis (a b : Bool) (hab : a ≠ b) (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 0 v (a :: b :: R) O A) = some (cfg 1 (some a, some b) R O A) := by
  cases a <;> cases b <;> simp_all [TM2.step, TM2.stepAux, prog, cfg] <;>
    (funext k; fin_cases k <;> simp)

theorem st0_one (a : Bool) (v : St) (O A : List Bool) :
    TM2.step prog (cfg 0 v [a] O A) = some (cfg 1 (some a, none) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st0_nil (v : St) (O A : List Bool) :
    TM2.step prog (cfg 0 v [] O A) = some (cfg 1 (none, none) [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st1_mark (v : St) (R O A : List Bool) :
    TM2.step prog (cfg 1 v R O (true :: A)) = some (cfg 2 (some true, v.2) R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st1_end (v : St) (R O : List Bool) :
    TM2.step prog (cfg 1 v R O []) = some (cfg 3 (none, v.2) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_cons (v : St) (a : Bool) (R O A : List Bool) :
    TM2.step prog (cfg 2 v (a :: R) O A) = some (cfg 1 v R O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st2_nil (v : St) (O A : List Bool) :
    TM2.step prog (cfg 2 v [] O A) = some (cfg 1 v [] O A) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st3_cons (v : St) (a : Bool) (R O : List Bool) :
    TM2.step prog (cfg 3 v (a :: R) O []) = some (cfg 4 (some a, v.2) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st3_nil (v : St) (O : List Bool) :
    TM2.step prog (cfg 3 v [] O []) = some (cfg 4 (none, v.2) [] O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st4_cons (h w : Option Bool) (b : Bool) (R O : List Bool) :
    TM2.step prog (cfg 4 (h, w) (b :: R) O []) = some (cfg 4 (h, some b) R O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st4_nil (h w : Option Bool) (O : List Bool) :
    TM2.step prog (cfg 4 (h, w) [] O []) = some (cfg 5 (h, none) [] O []) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem st5 (h w : Option Bool) (O : List Bool) :
    TM2.step prog (cfg 5 (h, w) [] O []) = some (hcfg ((h.getD false) :: O)) := by
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
    (hs : rn s c = some (hcfg O)) (ht : rn t c = some (hcfg P)) : O = P := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add hs] at ht
    obtain ⟨-, hK⟩ := rn_halted rfl ht
    have := congrArg (fun H : Cfg => H.stk 1) hK
    simpa [hcfg] using this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, rn_add ht] at hs
    obtain ⟨-, hK⟩ := rn_halted rfl hs
    have := congrArg (fun H : Cfg => H.stk 1) hK
    simpa [hcfg] using this.symm

theorem rep_succ_eq (k : ℕ) (A : List Bool) :
    List.replicate (k + 1) true ++ A = List.replicate k true ++ (true :: A) := by
  simp [List.replicate_succ', List.append_assoc]

/-- Phase 0 on a pair: the doubled instance is read two symbols at a time, each true bit leaves one
mark on the accumulator, and the separator leaves the witness on the input. -/
theorem p0pair (x w O A : List Bool) (v : St) :
    rn (x.length + 1) (cfg 0 v (MPP.PvsNP.pair x w) O A) =
      some (cfg 1 (some false, some true) w O (List.replicate (x.count true) true ++ A)) := by
  induction x generalizing A v with
  | nil =>
    have hp : MPP.PvsNP.pair [] w = false :: true :: w := by simp [MPP.PvsNP.pair]
    rw [hp]
    show rn (0 + 1) _ = _
    rw [rn_succ_step (st0_mis false true (by decide) v w O A)]
    simp [rn]
  | cons a x ih =>
    have hp : MPP.PvsNP.pair (a :: x) w = a :: a :: MPP.PvsNP.pair x w := by
      simp [MPP.PvsNP.pair, List.flatMap_cons]
    rw [hp]
    show rn ((x.length + 1) + 1) _ = _
    cases a
    · rw [rn_succ_step (st0_FF v (MPP.PvsNP.pair x w) O A), ih A (some false, some false)]
      simp [List.count_cons]
    · rw [rn_succ_step (st0_TT v (MPP.PvsNP.pair x w) O A), ih (true :: A) (some true, some true)]
      simp [List.count_cons, List.replicate_succ', List.append_assoc]

/-- Phase 0 on any input: it halts within `|R| + 1` steps, with at most `|R| / 2` marks. -/
theorem g0 : ∀ (R A : List Bool) (v : St) (O : List Bool), ∃ s, s ≤ R.length + 1 ∧
    ∃ (p q : Option Bool) (R' : List Bool) (k : ℕ), 2 * k ≤ R.length ∧ R'.length ≤ R.length ∧
      rn s (cfg 0 v R O A) = some (cfg 1 (p, q) R' O (List.replicate k true ++ A))
  | [], A, v, O => ⟨1, by simp, none, none, [], 0, by simp, by simp, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st0_nil v O A)]; simp [rn]⟩
  | [a], A, v, O => ⟨1, by simp, some a, none, [], 0, by simp, by simp, by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st0_one a v O A)]; simp [rn]⟩
  | a :: b :: R, A, v, O => by
    by_cases hab : a = b
    · subst hab
      cases a
      · obtain ⟨s, hs, p, q, R', k, hk, hR, h⟩ := g0 R A (some false, some false) O
        refine ⟨s + 1, by simp only [List.length_cons]; omega, p, q, R', k,
          by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega, ?_⟩
        rw [rn_succ_step (st0_FF v R O A)]
        exact h
      · obtain ⟨s, hs, p, q, R', k, hk, hR, h⟩ := g0 R (true :: A) (some true, some true) O
        refine ⟨s + 1, by simp only [List.length_cons]; omega, p, q, R', k + 1,
          by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega, ?_⟩
        rw [rn_succ_step (st0_TT v R O A), h, rep_succ_eq]
    · refine ⟨1, by simp, some a, some b, R, 0, by simp, by simp only [List.length_cons]; omega, ?_⟩
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st0_mis a b hab v R O A)]
      simp [rn]

/-- Phase 1: each mark drops one symbol of the input, so the input becomes its drop of the
number of marks. -/
theorem p1 : ∀ (k : ℕ) (R O : List Bool) (v : St),
    rn (2 * k + 1) (cfg 1 v R O (List.replicate k true)) =
      some (cfg 3 (none, v.2) (R.drop k) O [])
  | 0, R, O, v => by
    show rn (0 + 1) (cfg 1 v R O []) = _
    rw [rn_succ_step (st1_end v R O)]
    simp [rn]
  | k + 1, R, O, v => by
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by omega
    rw [e, List.replicate_succ, rn_succ_step (st1_mark v R O (List.replicate k true))]
    cases R with
    | nil =>
      rw [rn_succ_step (st2_nil (some true, v.2) O (List.replicate k true))]
      rw [p1 k [] O (some true, v.2)]
      simp
    | cons a R' =>
      rw [rn_succ_step (st2_cons (some true, v.2) a R' O (List.replicate k true))]
      rw [p1 k R' O (some true, v.2)]
      simp

/-- Phase 2 loop: the rest of the witness is consumed, one symbol per step. -/
theorem h4 : ∀ (R O : List Bool) (h w : Option Bool),
    rn (R.length + 1) (cfg 4 (h, w) R O []) = some (cfg 5 (h, none) [] O [])
  | [], O, h, w => by
    show rn (0 + 1) (cfg 4 (h, w) [] O []) = _
    rw [rn_succ_step (st4_nil h w O)]
    simp [rn]
  | b :: R, O, h, w => by
    show rn ((R.length + 1) + 1) (cfg 4 (h, w) (b :: R) O []) = _
    rw [rn_succ_step (st4_cons h w b R O)]
    exact h4 R O h (some b)

/-- Phase 2: the first witness symbol left is the answer, false if the witness is exhausted. -/
theorem p2 (I O : List Bool) (v : St) : ∃ s, s ≤ I.length + 3 ∧
    rn s (cfg 3 v I O []) = some (hcfg ((I.head?.getD false) :: O)) := by
  cases I with
  | nil =>
    have s3 : rn 1 (cfg 3 v [] O []) = some (cfg 4 (none, v.2) [] O []) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st3_nil v O)]
      simp [rn]
    have s4 := h4 [] O none v.2
    have s5 : rn 1 (cfg 5 (none, none) [] O []) = some (hcfg ((none : Option Bool).getD false :: O)) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st5 none none O)]
      simp [rn]
    exact ⟨1 + (([] : List Bool).length + 1) + 1, by simp, rn_trans (rn_trans s3 s4) s5⟩
  | cons a R =>
    have s3 : rn 1 (cfg 3 v (a :: R) O []) = some (cfg 4 (some a, v.2) R O []) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st3_cons v a R O)]
      simp [rn]
    have s4 := h4 R O (some a) v.2
    have s5 : rn 1 (cfg 5 (some a, none) [] O []) = some (hcfg ((some a).getD false :: O)) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (st5 (some a) none O)]
      simp [rn]
    exact ⟨1 + (R.length + 1) + 1, by simp only [List.length_cons]; omega,
      rn_trans (rn_trans s3 s4) s5⟩

theorem head_drop_getD (w : List Bool) (c : ℕ) :
    (w.drop c).head?.getD false = w.getD c false := by
  simp [List.head?_drop, List.getD_eq_getElem?_getD]

/-- The machine halts on every pair with the lookup bit. -/
theorem pair_run (x w : List Bool) : ∃ s,
    rn s (cfg 0 (none, none) (MPP.PvsNP.pair x w) [] []) = some (hcfg [w.getD (x.count true) false]) := by
  have h0 := p0pair x w [] [] (none, none)
  rw [List.append_nil] at h0
  have h1 := p1 (x.count true) w [] (some false, some true)
  obtain ⟨s2, -, h2⟩ := p2 (w.drop (x.count true)) [] (none, (some false, some true).2)
  have hc := rn_trans (rn_trans h0 h1) h2
  rw [head_drop_getD] at hc
  exact ⟨_, hc⟩

/-- Every input is processed in at most `3|z| + 5` steps, to a single output bit. -/
theorem gen (z : List Bool) : ∃ b : Bool, ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none) z [] []) = some (hcfg [b]) := by
  obtain ⟨s0, hs0, p, q, R', k, hk, hR, h0⟩ := g0 z [] (none, none) []
  rw [List.append_nil] at h0
  have h1 := p1 k R' [] (p, q)
  obtain ⟨s2, hs2, h2⟩ := p2 (R'.drop k) [] (none, (p, q).2)
  have hd := List.length_drop (i := k) (l := R')
  refine ⟨(R'.drop k).head?.getD false, s0 + (2 * k + 1) + s2, ?_, ?_⟩
  · omega
  · exact rn_trans (rn_trans h0 h1) h2

/-- The lookup bit on an input, chosen from `gen`. -/
noncomputable def lookupBit (z : List Bool) : Bool := (gen z).choose

theorem lookupBit_spec (z : List Bool) : ∃ s, s ≤ 3 * z.length + 5 ∧
    rn s (cfg 0 (none, none) z [] []) = some (hcfg [lookupBit z]) :=
  (gen z).choose_spec

theorem lookupBit_pair (x w : List Bool) :
    lookupBit (MPP.PvsNP.pair x w) = w.getD (x.count true) false := by
  obtain ⟨s1, -, h1⟩ := lookupBit_spec (MPP.PvsNP.pair x w)
  obtain ⟨s2, h2⟩ := pair_run x w
  have := rn_unique h1 h2
  simpa using this

theorem initList_eq (z : List Bool) : initList tm z = cfg 0 (none, none) z [] [] := by
  unfold initList cfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

theorem haltList_eq (O : List Bool) : haltList tm O = hcfg O := by
  unfold haltList hcfg
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tm]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool lookupBit where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 3 * Polynomial.X + 5
  outputsFun z := by
    have key : (fun o => o.bind (TM2.step prog))^[(lookupBit_spec z).choose] (some (initList tm z)) =
        some (haltList tm [lookupBit z]) := by
      rw [initList_eq, haltList_eq]
      exact (lookupBit_spec z).choose_spec.2
    refine ⟨⟨(lookupBit_spec z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      have := (lookupBit_spec z).choose_spec.1
      omega

theorem main : ∃ L : Lang, InP L ∧ ∀ x w : List Bool, L (pair x w) = w.getD (x.count true) false :=
  ⟨lookupBit, ⟨machine⟩, lookupBit_pair⟩

end MPP.Solutions.Pnp134
