import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp119

open MPP.PvsNP Computability Turing

/-- One symbol of the postfix program on the stack `s`, with the top first. A false symbol pushes
`true`. A true symbol pops the two top values (a missing value counts as `false`) and pushes their
NAND. -/
def stepL (s : List Bool) (b : Bool) : List Bool :=
  if b then (!(s.headD false && (s.drop 1).headD false)) :: s.drop 2 else true :: s

/-- The evaluator: the answer is the top of the stack after the whole input, or `false` if the stack
is empty. -/
def ans (x : List Bool) : Bool := (x.foldl stepL []).headD false

/-- Program of the evaluator. Label 0 reads one input symbol into the state, as `(value, none)`.
Labels 1, 5 and 6 pop the two top values of the work stack (stack 2) into the state and push their
NAND. Label 2 pushes `true`. Labels 3, 4 and 7 move the top value to the output and clear the work
stack before halting. -/
def prog : Fin 8 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some false) (.goto fun _ => 2)
        (.branch (fun s => s.1 = some true) (.goto fun _ => 1) (.goto fun _ => 3)))
  | 1 => .pop 2 (fun _ h => (h, none)) (.goto fun _ => 5)
  | 2 => .push 2 (fun _ => true) (.goto fun _ => 0)
  | 3 => .pop 2 (fun _ h => (h, none)) (.goto fun _ => 4)
  | 4 => .push 1 (fun s => s.1.getD false) (.goto fun _ => 7)
  | 5 => .pop 2 (fun s h => (s.1, h)) (.goto fun _ => 6)
  | 6 => .push 2 (fun s => !(s.1.getD false && s.2.getD false)) (.goto fun _ => 0)
  | 7 => .pop 2 (fun _ h => (h, none))
      (.branch (fun s => s.1.isSome) (.goto fun _ => 7) (.load (fun _ => (none, none)) .halt))

/-- The evaluator as a finite machine: stacks `0` (input), `1` (output), `2` (work stack). -/
def tm : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 8
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := prog

/-- Configuration with label `l`, state `v`, input `R`, output `O`, work stack `B`. -/
def cfg (l : Fin 8) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, B]⟩

theorem t0_false (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 0 v (false :: R) O B) = some (cfg 2 (some false, none) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t0_true (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 0 v (true :: R) O B) = some (cfg 1 (some true, none) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t0_nil (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step prog (cfg 0 v [] O B) = some (cfg 3 (none, none) [] O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t1 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 1 v R O B) = some (cfg 5 (B.head?, none) R O B.tail) := by
  cases B <;> simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t2 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 2 v R O B) = some (cfg 0 v R O (true :: B)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t3 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 3 v R O B) = some (cfg 4 (B.head?, none) R O B.tail) := by
  cases B <;> simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t4 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 4 v R O B) = some (cfg 7 v R (v.1.getD false :: O) B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t5 (a b : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 5 (a, b) R O B) = some (cfg 6 (a, B.head?) R O B.tail) := by
  cases B <;> simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t6 (a b : Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 6 (a, b) R O B) =
      some (cfg 0 (a, b) R O ((!(a.getD false && b.getD false)) :: B)) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t7_cons (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step prog (cfg 7 v R O (a :: B)) = some (cfg 7 (some a, none) R O B) := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

theorem t7_nil (v : Option Bool × Option Bool) (R O : List Bool) :
    TM2.step prog (cfg 7 v R O []) = some ⟨none, (none, none), ![R, O, []]⟩ := by
  simp [TM2.step, TM2.stepAux, prog, cfg] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step prog))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool)}
    (h : TM2.step prog c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 8) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Clearing phase at label 7: the work stack is popped and the machine halts with the output
unchanged. It takes `|W| + 1` steps. -/
theorem clear7 : ∀ (W : List Bool) (v : Option Bool × Option Bool) (O : List Bool),
    rn (W.length + 1) (cfg 7 v [] O W) = some ⟨none, (none, none), ![[], O, []]⟩
  | [], v, O => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (t7_nil v [] O)]
      simp [rn]
  | a :: W, v, O => by
      rw [show (a :: W).length + 1 = (W.length + 1) + 1 from rfl,
        rn_succ_step (t7_cons a v [] O W)]
      exact clear7 W (some a, none) O

/-- Final phase: the top of the work stack is moved to the output, then the rest is cleared. -/
theorem final : ∀ (W : List Bool) (v : Option Bool × Option Bool), ∃ n, n ≤ W.length + 3 ∧
    rn n (cfg 3 v [] [] W) = some ⟨none, (none, none), ![[], [W.headD false], []]⟩
  | [], v => ⟨3, by simp, by
      show rn (2 + 1) (cfg 3 v [] [] []) = _
      rw [rn_succ_step (t3 v [] [] [])]
      show rn (1 + 1) _ = _
      rw [rn_succ_step (t4 _ [] [] _)]
      simpa using clear7 [] (none, none) [false]⟩
  | a :: W, v => ⟨W.length + 3, by simp, by
      show rn (W.length + 1 + 1 + 1) (cfg 3 v [] [] (a :: W)) = _
      rw [rn_succ_step (t3 v [] [] (a :: W))]
      show rn (W.length + 1 + 1) _ = _
      rw [rn_succ_step (t4 _ [] [] _)]
      simpa using clear7 W (some a, none) [a]⟩

theorem hd_eq (s : List Bool) : s.head?.getD false = s.headD false := by
  cases s <;> rfl

theorem hd2_eq (s : List Bool) : (s.tail.head?).getD false = (s.drop 1).headD false := by
  cases s with
  | nil => rfl
  | cons h t => cases t <;> rfl

theorem stepL_len (s : List Bool) (b : Bool) : (stepL s b).length ≤ s.length + 1 := by
  cases b <;> simp [stepL] <;> omega

theorem foldl_len : ∀ (x s : List Bool), (x.foldl stepL s).length ≤ s.length + x.length
  | [], s => by simp
  | b :: x, s => by
      have ih := foldl_len x (stepL s b)
      have hl := stepL_len s b
      simp only [List.foldl_cons, List.length_cons]
      omega

/-- Scanning phase: each input symbol is read into the work stack, a true symbol first popping the
two top values. The machine stops at label 3 with the input consumed. It takes at most
`4|x| + 1` steps. -/
theorem run : ∀ (x : List Bool) (v : Option Bool × Option Bool) (s : List Bool),
    ∃ n, n ≤ 4 * x.length + 1 ∧ ∃ v' : Option Bool × Option Bool,
      rn n (cfg 0 v x [] s) = some (cfg 3 v' [] [] (x.foldl stepL s))
  | [], v, s => ⟨1, by simp, (none, none), by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (t0_nil v [] s)]
      simp [rn]⟩
  | false :: x, v, s => by
      obtain ⟨n, hn, v', h⟩ := run x (some false, none) (true :: s)
      refine ⟨n + 1 + 1, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [rn_succ_step (t0_false v x [] s), rn_succ_step (t2 (some false, none) x [] s), h]
      simp [List.foldl_cons, stepL]
  | true :: x, v, s => by
      have key : (!((s.head?).getD false && (s.tail.head?).getD false)) :: s.tail.tail =
          stepL s true := by
        rcases s with _ | ⟨a, t⟩
        · simp [stepL]
        · rcases t with _ | ⟨b, u⟩ <;> simp [stepL]
      obtain ⟨n, hn, v', h⟩ := run x (s.head?, s.tail.head?) (stepL s true)
      refine ⟨n + 1 + 1 + 1 + 1, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [rn_succ_step (t0_true v x [] s), rn_succ_step (t1 (some true, none) x [] s),
        rn_succ_step (t5 _ none x [] _), rn_succ_step (t6 _ _ x [] _), key, h]
      simp [List.foldl_cons]

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

/-- Every input is evaluated by the machine in at most `5|x| + 4` steps. -/
theorem gen (x : List Bool) : ∃ n, n ≤ 5 * x.length + 4 ∧
    rn n (cfg 0 (none, none) x [] []) = some ⟨none, (none, none), ![[], [ans x], []]⟩ := by
  obtain ⟨n1, hn1, v1, h1⟩ := run x (none, none) []
  obtain ⟨n2, hn2, h2⟩ := final (x.foldl stepL []) v1
  have hl := foldl_len x []
  refine ⟨n2 + n1, ?_, ?_⟩
  · simp only [List.length_nil, Nat.zero_add] at hl
    omega
  · rw [rn_add (n := n2) h1]
    exact h2

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool ans where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 5 * Polynomial.X + 4
  outputsFun z := by
    have hs := (gen z).choose_spec.1
    have he := (gen z).choose_spec.2
    have key : (fun o => o.bind (TM2.step prog))^[(gen z).choose]
        (some (initList tm z)) = some (haltList tm (encodeBool (ans z))) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tm) (List.map_id z)
        | exact congrArg (fun l => some (haltList tm l)) (List.map_id (encodeBool (ans z)))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : InP (fun x : List Bool => (x.foldl (fun (s : List Bool) (b : Bool) =>
      if b then (!(s.headD false && (s.drop 1).headD false)) :: s.drop 2 else true :: s) []).headD false) :=
  ⟨machine⟩

end MPP.Solutions.Pnp119
