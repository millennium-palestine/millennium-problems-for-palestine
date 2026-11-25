import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp021
import MPP.Solutions.Pnp025
import MPP.Solutions.Pnp026

namespace MPP.Solutions.Pnp123

open MPP.PvsNP Computability Turing

/-- One symbol of the program with witness leaves, on the state `(work, witness)`. A true symbol pops
the two top values of the work stack and pushes their NAND. A false symbol pushes the top of the
witness, or `false` when the witness has run out, and drops it from the witness. -/
def stepP (st : List Bool × List Bool) (b : Bool) : List Bool × List Bool :=
  if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2)
  else (st.2.headD false :: st.1, st.2.drop 1)

/-- The split of a pair encoding into its doubled first component and the rest, scanning two symbols
at a time. On `pair w x` it gives `(w, x)`. -/
def scan : List Bool → List Bool × List Bool
  | a :: b :: rest => if a = b then (a :: (scan rest).1, (scan rest).2) else ([], rest)
  | _ => ([], [])

/-- The verifier in the witness-first order: the witness is the first component of the pair. -/
def evalW (z : List Bool) : Bool := ((scan z).2.foldl stepP ([], (scan z).1)).1.headD false

/-- Program of the witness-first verifier. Stacks: `0` input, `1` output, `2` accumulator, `3`
witness, `4` work. Labels 0 to 2 scan the doubled bits of the witness into the accumulator. Label 3
moves the accumulator onto the witness, which restores its order. Labels 4 to 8 evaluate the rest of
the input, as `stepP`. Labels 9 to 11 write the top of the work stack to the output and clear the
work and witness stacks before halting. -/
def progW : Fin 12 → TM2.Stmt (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some false) (.goto fun _ => 1)
        (.branch (fun s => s.1 = some true) (.goto fun _ => 2) (.goto fun _ => 3)))
  | 1 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some false) (.push 2 (fun _ => false) (.goto fun _ => 0))
        (.goto fun _ => 3))
  | 2 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some true) (.push 2 (fun _ => true) (.goto fun _ => 0))
        (.goto fun _ => 3))
  | 3 => .pop 2 (fun _ h => (h, none))
      (.branch (fun s => s.1.isSome) (.push 3 (fun s => s.1.getD false) (.goto fun _ => 3))
        (.goto fun _ => 4))
  | 4 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some false) (.goto fun _ => 5)
        (.branch (fun s => s.1 = some true) (.goto fun _ => 6) (.goto fun _ => 9)))
  | 5 => .pop 3 (fun _ h => (h, none)) (.push 4 (fun s => s.1.getD false) (.goto fun _ => 4))
  | 6 => .pop 4 (fun _ h => (h, none)) (.goto fun _ => 7)
  | 7 => .pop 4 (fun s h => (s.1, h)) (.goto fun _ => 8)
  | 8 => .push 4 (fun s => !(s.1.getD false && s.2.getD false)) (.goto fun _ => 4)
  | 9 => .pop 4 (fun _ h => (h, none))
      (.push 1 (fun s => s.1.getD false) (.goto fun _ => 10))
  | 10 => .pop 4 (fun _ h => (h, none))
      (.branch (fun s => s.1.isSome) (.goto fun _ => 10) (.goto fun _ => 11))
  | 11 => .pop 3 (fun _ h => (h, none))
      (.branch (fun s => s.1.isSome) (.goto fun _ => 11)
        (.load (fun _ => (none, none)) .halt))

/-- The witness-first verifier as a finite machine. -/
def tmW : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 12
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := progW

/-- Configuration with label `l`, state `v`, input `R`, output `O`, accumulator `A`, witness `W` and
work stack `E`. -/
def cfgW (l : Fin 12) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, A, W, E]⟩

theorem s0_false (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 0 v (false :: R) O A W E) = some (cfgW 1 (some false, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s0_true (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 0 v (true :: R) O A W E) = some (cfgW 2 (some true, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s0_nil (v : Option Bool × Option Bool) (O A W E : List Bool) :
    TM2.step progW (cfgW 0 v [] O A W E) = some (cfgW 3 (none, none) [] O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s1_false (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 1 v (false :: R) O A W E) =
      some (cfgW 0 (some false, none) R O (false :: A) W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s1_true (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 1 v (true :: R) O A W E) = some (cfgW 3 (some true, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s1_nil (v : Option Bool × Option Bool) (O A W E : List Bool) :
    TM2.step progW (cfgW 1 v [] O A W E) = some (cfgW 3 (none, none) [] O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s2_true (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 2 v (true :: R) O A W E) =
      some (cfgW 0 (some true, none) R O (true :: A) W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s2_false (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 2 v (false :: R) O A W E) = some (cfgW 3 (some false, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem s2_nil (v : Option Bool × Option Bool) (O A W E : List Bool) :
    TM2.step progW (cfgW 2 v [] O A W E) = some (cfgW 3 (none, none) [] O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem p3_push (a : Bool) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 3 v R O (a :: A) W E) = some (cfgW 3 (some a, none) R O A (a :: W) E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem p3_end (v : Option Bool × Option Bool) (R O W E : List Bool) :
    TM2.step progW (cfgW 3 v R O [] W E) = some (cfgW 4 (none, none) R O [] W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e4_false (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 4 v (false :: R) O A W E) = some (cfgW 5 (some false, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e4_true (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 4 v (true :: R) O A W E) = some (cfgW 6 (some true, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e4_nil (v : Option Bool × Option Bool) (O A W E : List Bool) :
    TM2.step progW (cfgW 4 v [] O A W E) = some (cfgW 9 (none, none) [] O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e5_cons (a : Bool) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 5 v R O A (a :: W) E) = some (cfgW 4 (some a, none) R O A W (a :: E)) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e5_nil (v : Option Bool × Option Bool) (R O A E : List Bool) :
    TM2.step progW (cfgW 5 v R O A [] E) = some (cfgW 4 (none, none) R O A [] (false :: E)) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e6_cons (a : Bool) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 6 v R O A W (a :: E)) = some (cfgW 7 (some a, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e6_nil (v : Option Bool × Option Bool) (R O A W : List Bool) :
    TM2.step progW (cfgW 6 v R O A W []) = some (cfgW 7 (none, none) R O A W []) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e7_cons (a c : Option Bool) (b : Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 7 (a, c) R O A W (b :: E)) = some (cfgW 8 (a, some b) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e7_nil (a : Option Bool) (c : Option Bool) (R O A W : List Bool) :
    TM2.step progW (cfgW 7 (a, c) R O A W []) = some (cfgW 8 (a, none) R O A W []) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem e8 (a b : Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 8 (a, b) R O A W E) =
      some (cfgW 4 (a, b) R O A W ((!(a.getD false && b.getD false)) :: E)) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f9 (v : Option Bool × Option Bool) (R O A W : List Bool) (a : Bool) (E : List Bool) :
    TM2.step progW (cfgW 9 v R O A W (a :: E)) =
      some (cfgW 10 (some a, none) R (a :: O) A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f9_nil (v : Option Bool × Option Bool) (R O A W : List Bool) :
    TM2.step progW (cfgW 9 v R O A W []) = some (cfgW 10 (none, none) R (false :: O) A W []) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f10_cons (a : Bool) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 10 v R O A W (a :: E)) = some (cfgW 10 (some a, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f10_nil (v : Option Bool × Option Bool) (R O A W : List Bool) :
    TM2.step progW (cfgW 10 v R O A W []) = some (cfgW 11 (none, none) R O A W []) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f11_cons (a : Bool) (v : Option Bool × Option Bool) (R O A W E : List Bool) :
    TM2.step progW (cfgW 11 v R O A (a :: W) E) = some (cfgW 11 (some a, none) R O A W E) := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

theorem f11_nil (v : Option Bool × Option Bool) (R O A E : List Bool) :
    TM2.step progW (cfgW 11 v R O A [] E) = some ⟨none, (none, none), ![R, O, A, [], E]⟩ := by
  simp [TM2.step, TM2.stepAux, progW, cfgW] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step progW))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool)}
    (h : TM2.step progW c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 5 => Bool) (Fin 12) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

theorem scan_nil : scan [] = ([], []) := rfl

theorem scan_one (a : Bool) : scan [a] = ([], []) := rfl

theorem scan_ff (w : List Bool) : scan (false :: false :: w) = (false :: (scan w).1, (scan w).2) := by
  simp [scan]

theorem scan_ft (w : List Bool) : scan (false :: true :: w) = ([], w) := by
  simp [scan]

theorem scan_tf (w : List Bool) : scan (true :: false :: w) = ([], w) := by
  simp [scan]

theorem scan_tt (w : List Bool) : scan (true :: true :: w) = (true :: (scan w).1, (scan w).2) := by
  simp [scan]

/-- Scanning phase: the doubled bits are moved onto the accumulator, and the machine stops at label 3
with the rest of the input. It takes at most `|z| + 1` steps. -/
theorem phaseA : ∀ (z : List Bool) (v : Option Bool × Option Bool) (O A W E : List Bool),
    ∃ n, n ≤ z.length + 1 ∧ ∃ v' : Option Bool × Option Bool,
      rn n (cfgW 0 v z O A W E) = some (cfgW 3 v' (scan z).2 O ((scan z).1.reverse ++ A) W E)
  | [], v, O, A, W, E => ⟨1, by simp, (none, none), by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (s0_nil v O A W E)]
      simp [rn, scan_nil]⟩
  | [false], v, O, A, W, E => ⟨2, by simp, (none, none), by
      rw [show (2 : ℕ) = 1 + 1 from rfl, rn_succ_step (s0_false v [] O A W E),
        rn_succ_step (s1_nil _ O A W E)]
      simp [rn, scan_one]⟩
  | [true], v, O, A, W, E => ⟨2, by simp, (none, none), by
      rw [show (2 : ℕ) = 1 + 1 from rfl, rn_succ_step (s0_true v [] O A W E),
        rn_succ_step (s2_nil _ O A W E)]
      simp [rn, scan_one]⟩
  | false :: false :: w, v, O, A, W, E => by
      obtain ⟨s, hs, v', h⟩ := phaseA w (some false, none) O (false :: A) W E
      refine ⟨s + 2, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [show s + 2 = (s + 1) + 1 from rfl, rn_succ_step (s0_false v (false :: w) O A W E),
        rn_succ_step (s1_false (some false, none) w O A W E), h, scan_ff]
      simp [List.reverse_cons, List.append_assoc]
  | false :: true :: w, v, O, A, W, E => ⟨2, by simp only [List.length_cons]; omega, (some true, none), by
      rw [show (2 : ℕ) = 1 + 1 from rfl, rn_succ_step (s0_false v (true :: w) O A W E),
        rn_succ_step (s1_true (some false, none) w O A W E), scan_ft]
      simp [rn]⟩
  | true :: false :: w, v, O, A, W, E => ⟨2, by simp only [List.length_cons]; omega, (some false, none), by
      rw [show (2 : ℕ) = 1 + 1 from rfl, rn_succ_step (s0_true v (false :: w) O A W E),
        rn_succ_step (s2_false (some true, none) w O A W E), scan_tf]
      simp [rn]⟩
  | true :: true :: w, v, O, A, W, E => by
      obtain ⟨s, hs, v', h⟩ := phaseA w (some true, none) O (true :: A) W E
      refine ⟨s + 2, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [show s + 2 = (s + 1) + 1 from rfl, rn_succ_step (s0_true v (true :: w) O A W E),
        rn_succ_step (s2_true (some true, none) w O A W E), h, scan_tt]
      simp [List.reverse_cons, List.append_assoc]

/-- Moving phase: the accumulator is moved onto the witness stack, which restores the order of the
witness. The machine reaches label 4 with the accumulator empty. -/
theorem phaseB : ∀ (A R O W E : List Bool) (v : Option Bool × Option Bool),
    rn (A.length + 1) (cfgW 3 v R O A W E) = some (cfgW 4 (none, none) R O [] (A.reverse ++ W) E)
  | [], R, O, W, E, v => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (p3_end v R O W E)]
      simp [rn]
  | a :: A, R, O, W, E, v => by
      rw [show (a :: A).length + 1 = (A.length + 1) + 1 from rfl, rn_succ_step (p3_push a v R O A W E)]
      rw [phaseB A R O (a :: W) E (some a, none)]
      simp [List.reverse_cons, List.append_assoc]

theorem hd_eq (s : List Bool) : s.head?.getD false = s.headD false := by
  cases s <;> rfl

/-- The four steps of a true symbol: two operands are popped from the work stack and their NAND is
pushed back, with the state holding the two operands. -/
theorem tstep (v : Option Bool × Option Bool) (O W x : List Bool) (E : List Bool) :
    rn 4 (cfgW 4 v (true :: x) O [] W E) = some (cfgW 4 (E.head?, E.tail.head?) x O [] W
      ((!((E.head?).getD false && (E.tail.head?).getD false)) :: E.tail.tail)) := by
  rcases E with _ | ⟨a, _ | ⟨b, E2⟩⟩
  · show rn (3 + 1) _ = _
    rw [rn_succ_step (e4_true v x O [] W [])]
    show rn (2 + 1) _ = _
    rw [rn_succ_step (e6_nil _ x O [] W)]
    show rn (1 + 1) _ = _
    rw [rn_succ_step (e7_nil none none x O [] W)]
    show rn (0 + 1) _ = _
    rw [rn_succ_step (e8 none none x O [] W [])]
    simp [rn]
  · show rn (3 + 1) _ = _
    rw [rn_succ_step (e4_true v x O [] W [a])]
    show rn (2 + 1) _ = _
    rw [rn_succ_step (e6_cons a _ x O [] W [])]
    show rn (1 + 1) _ = _
    rw [rn_succ_step (e7_nil (some a) none x O [] W)]
    show rn (0 + 1) _ = _
    rw [rn_succ_step (e8 (some a) none x O [] W [])]
    simp [rn]
  · show rn (3 + 1) _ = _
    rw [rn_succ_step (e4_true v x O [] W (a :: b :: E2))]
    show rn (2 + 1) _ = _
    rw [rn_succ_step (e6_cons a _ x O [] W (b :: E2))]
    show rn (1 + 1) _ = _
    rw [rn_succ_step (e7_cons (some a) none b x O [] W E2)]
    show rn (0 + 1) _ = _
    rw [rn_succ_step (e8 (some a) (some b) x O [] W E2)]
    simp [rn]

/-- Evaluation phase: label 4 reads the rest of the input, one symbol at a time, and the state is the
pair of the work stack and the witness, as in `stepP`. It takes at most `4|x| + 1` steps. -/
theorem phaseE : ∀ (x : List Bool) (v : Option Bool × Option Bool) (O W E : List Bool),
    ∃ n, n ≤ 4 * x.length + 1 ∧ ∃ v' : Option Bool × Option Bool,
      rn n (cfgW 4 v x O [] W E) =
        some (cfgW 9 v' [] O [] (x.foldl stepP (E, W)).2 (x.foldl stepP (E, W)).1)
  | [], v, O, W, E => ⟨1, by simp, (none, none), by
      rw [show (1 : ℕ) = 0 + 1 from rfl, rn_succ_step (e4_nil v O [] W E)]
      simp [rn]⟩
  | false :: x, v, O, [], E => by
      obtain ⟨n, hn, v', h⟩ := phaseE x (none, none) O [] (false :: E)
      refine ⟨n + 1 + 1, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [rn_succ_step (e4_false v x O [] [] E), rn_succ_step (e5_nil _ x O [] E), h]
      simp [List.foldl_cons, stepP]
  | false :: x, v, O, a :: W, E => by
      obtain ⟨n, hn, v', h⟩ := phaseE x (some a, none) O W (a :: E)
      refine ⟨n + 1 + 1, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [rn_succ_step (e4_false v x O [] (a :: W) E), rn_succ_step (e5_cons a _ x O [] W E), h]
      simp [List.foldl_cons, stepP]
  | true :: x, v, O, W, E => by
      obtain ⟨n, hn, v', h⟩ := phaseE x (E.head?, E.tail.head?) O W
        ((!((E.head?).getD false && (E.tail.head?).getD false)) :: E.tail.tail)
      refine ⟨n + 4, by simp only [List.length_cons]; omega, v', ?_⟩
      rw [rn_add (n := n) (tstep v O W x E), h]
      have hst : stepP (E, W) true =
          ((!((E.head?).getD false && (E.tail.head?).getD false)) :: E.tail.tail, W) := by
        rcases E with _ | ⟨a, t⟩
        · simp [stepP]
        · rcases t with _ | ⟨b, u⟩ <;> simp [stepP]
      rw [List.foldl_cons, hst]

theorem scan_pair : ∀ x u : List Bool, scan (pair x u) = (x, u)
  | [], u => by simp [pair, scan]
  | b :: x, u => by
      have e : pair (b :: x) u = b :: b :: pair x u := by simp [pair]
      rw [e]
      simp [scan, scan_pair x u]

theorem scan_len : ∀ w : List Bool, (scan w).1.length + (scan w).2.length ≤ w.length
  | [] => by simp [scan]
  | [a] => by simp [scan]
  | a :: b :: rest => by
      have ih := scan_len rest
      by_cases h : a = b
      · subst h
        simp [scan] <;> omega
      · simp [scan, h] <;> omega

theorem stepP_len (st : List Bool × List Bool) (b : Bool) :
    (stepP st b).1.length + (stepP st b).2.length ≤ st.1.length + st.2.length + 1 := by
  cases b <;> simp [stepP] <;> omega

theorem foldl_len : ∀ (x : List Bool) (st : List Bool × List Bool),
    (x.foldl stepP st).1.length + (x.foldl stepP st).2.length ≤
      st.1.length + st.2.length + x.length
  | [], st => by simp
  | b :: x, st => by
      have ih := foldl_len x (stepP st b)
      have hl := stepP_len st b
      simp only [List.foldl_cons, List.length_cons]
      omega

/-- Clearing the work stack: label 10 pops it, one symbol at a time. -/
theorem clear10 : ∀ (E : List Bool) (v : Option Bool × Option Bool) (O W : List Bool),
    rn (E.length + 1) (cfgW 10 v [] O [] W E) = some (cfgW 11 (none, none) [] O [] W [])
  | [], v, O, W => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (f10_nil v [] O [] W)]
      simp [rn]
  | a :: E, v, O, W => by
      rw [show (a :: E).length + 1 = (E.length + 1) + 1 from rfl,
        rn_succ_step (f10_cons a v [] O [] W E)]
      exact clear10 E _ O W

/-- Clearing the witness stack, then halting with the output unchanged. -/
theorem clear11 : ∀ (W : List Bool) (v : Option Bool × Option Bool) (O : List Bool),
    rn (W.length + 1) (cfgW 11 v [] O [] W []) = some ⟨none, (none, none), ![[], O, [], [], []]⟩
  | [], v, O => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (f11_nil v [] O [] [])]
      simp [rn]
  | a :: W, v, O => by
      rw [show (a :: W).length + 1 = (W.length + 1) + 1 from rfl,
        rn_succ_step (f11_cons a v [] O [] W [])]
      exact clear11 W _ O

/-- Final phase: the top of the work stack is written to the output, and the two stacks are cleared.
It takes at most `|E| + |W| + 3` steps. -/
theorem fin (E W : List Bool) (v : Option Bool × Option Bool) : ∃ n, n ≤ E.length + W.length + 3 ∧
    rn n (cfgW 9 v [] [] [] W E) = some ⟨none, (none, none), ![[], [E.headD false], [], [], []]⟩ := by
  cases E with
  | nil =>
    have h1 : rn (0 + 1 + 1) (cfgW 9 v [] [] [] W []) = some (cfgW 11 (none, none) [] [false] [] W []) := by
      rw [rn_succ_step (f9_nil v [] [] [] W)]
      exact clear10 [] _ [false] W
    have h2 := clear11 W (none, none) [false]
    refine ⟨(W.length + 1) + (0 + 1 + 1), by simp only [List.length_nil]; omega, ?_⟩
    rw [rn_add (n := W.length + 1) h1]
    simpa using h2
  | cons a E' =>
    have h1 : rn (E'.length + 1 + 1) (cfgW 9 v [] [] [] W (a :: E')) =
        some (cfgW 11 (none, none) [] [a] [] W []) := by
      rw [rn_succ_step (f9 v [] [] [] W a E')]
      exact clear10 E' _ [a] W
    have h2 := clear11 W (none, none) [a]
    refine ⟨(W.length + 1) + (E'.length + 1 + 1), by simp only [List.length_cons]; omega, ?_⟩
    rw [rn_add (n := W.length + 1) h1]
    simpa using h2

/-- Every input is evaluated by the machine in at most `6|z| + 6` steps. -/
theorem gen (z : List Bool) : ∃ n, n ≤ 6 * z.length + 6 ∧
    rn n (cfgW 0 (none, none) z [] [] [] []) = some ⟨none, (none, none), ![[], [evalW z], [], [], []]⟩ := by
  obtain ⟨n1, hn1, v1, h1⟩ := phaseA z (none, none) [] [] [] []
  rw [List.append_nil] at h1
  have h2 := phaseB (scan z).1.reverse (scan z).2 [] [] [] v1
  rw [List.reverse_reverse, List.append_nil] at h2
  obtain ⟨n3, hn3, v3, h3⟩ := phaseE (scan z).2 (none, none) [] (scan z).1 []
  obtain ⟨n4, hn4, h4⟩ := fin ((scan z).2.foldl stepP ([], (scan z).1)).1
    ((scan z).2.foldl stepP ([], (scan z).1)).2 v3
  have hl := foldl_len (scan z).2 ([], (scan z).1)
  have hs := scan_len z
  have hA : rn ((scan z).1.reverse.length + 1 + n1) (cfgW 0 (none, none) z [] [] [] []) =
      some (cfgW 4 (none, none) (scan z).2 [] [] (scan z).1 []) := by
    rw [rn_add (n := (scan z).1.reverse.length + 1) h1]
    exact h2
  have hB : rn (n3 + ((scan z).1.reverse.length + 1 + n1)) (cfgW 0 (none, none) z [] [] [] []) =
      some (cfgW 9 v3 [] [] [] ((scan z).2.foldl stepP ([], (scan z).1)).2
        ((scan z).2.foldl stepP ([], (scan z).1)).1) := by
    rw [rn_add (n := n3) hA]
    exact h3
  refine ⟨n4 + (n3 + ((scan z).1.reverse.length + 1 + n1)), ?_, ?_⟩
  · simp only [List.length_reverse, List.length_nil, Nat.zero_add] at hl ⊢
    omega
  · rw [rn_add (n := n4) hB]
    exact h4

theorem initList_eq (z : List Bool) : initList tmW z = cfgW 0 (none, none) z [] [] [] [] := by
  unfold initList cfgW
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tmW]

theorem haltList_eq (O : List Bool) :
    haltList tmW O = ⟨none, (none, none), ![[], O, [], [], []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 5) => ?_
  fin_cases k <;> simp [tmW]

noncomputable def machine :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool evalW where
  tm := tmW
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 6 * Polynomial.X + 6
  outputsFun z := by
    have hs := (gen z).choose_spec.1
    have he := (gen z).choose_spec.2
    have key : (fun o => o.bind (TM2.step progW))^[(gen z).choose]
        (some (initList tmW z)) = some (haltList tmW (encodeBool (evalW z))) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(gen z).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tmW) (List.map_id z)
        | exact congrArg (fun l => some (haltList tmW l)) (List.map_id (encodeBool (evalW z)))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

theorem main : ∃ V : Lang, InP V ∧ ∀ x w : List Bool,
    V (pair x w) = (x.foldl (fun (st : List Bool × List Bool) (b : Bool) =>
      if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2)
      else (st.2.headD false :: st.1, st.2.drop 1)) ([], w)).1.headD false := by
  obtain ⟨e, ⟨he⟩, heq⟩ := MPP.Solutions.Pnp025.main
  obtain ⟨d, ⟨hd⟩, hdeq⟩ := MPP.Solutions.Pnp021.main
  obtain ⟨S, ⟨hS⟩, hSeq⟩ := MPP.Solutions.Pnp026.main e d ⟨he⟩ ⟨hd⟩
  have hV : InP evalW := ⟨machine⟩
  obtain ⟨hV'⟩ := hV
  obtain ⟨hC⟩ := MPP.Solutions.Pnp006.main hS hV'
  refine ⟨evalW ∘ S, ⟨hC⟩, fun x w => ?_⟩
  simp only [Function.comp, hSeq, heq, hdeq]
  unfold evalW
  rw [scan_pair]
  rfl

end MPP.Solutions.Pnp123
