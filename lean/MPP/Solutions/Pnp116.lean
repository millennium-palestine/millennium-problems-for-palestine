import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp115

namespace MPP.Solutions.Pnp116

open MPP.PvsNP Computability Turing

/-- The decision of a list of bits: it is accepted exactly when no symbol is false. -/
def qf (y : List Bool) : Bool := decide (false ∉ y)

/-- Program of the no-false test. Label 0 reads one input symbol into the state. A false symbol
goes to label 1, which drains the rest of the input, and then writes `false` (label 3). A true symbol
returns to label 0. The end of the input writes `true` (label 2). Labels 2 and 3 push the answer to
the output and label 4 halts. -/
def progQ : Fin 5 → TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)
  | 0 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1 = some false) (.goto fun _ => 1)
        (.branch (fun s => s.1.isSome) (.goto fun _ => 0) (.goto fun _ => 2)))
  | 1 => .pop 0 (fun _ h => (h, none))
      (.branch (fun s => s.1.isSome) (.goto fun _ => 1) (.goto fun _ => 3))
  | 2 => .push 1 (fun _ => true) (.goto fun _ => 4)
  | 3 => .push 1 (fun _ => false) (.goto fun _ => 4)
  | 4 => .load (fun _ => (none, none)) .halt

/-- The no-false test as a finite machine: stacks `0` (input), `1` (output), `2` (unused). -/
def tmQ : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 5
  main := 0
  σ := Option Bool × Option Bool
  initialState := (none, none)
  m := progQ

/-- Configuration with label `l`, state `v`, input `R`, output `O`, spare stack `B`. -/
def cfgQ (l : Fin 5) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool) :=
  ⟨some l, v, ![R, O, B]⟩

theorem q0_false (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 0 v (false :: R) O B) = some (cfgQ 1 (some false, none) R O B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q0_true (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 0 v (true :: R) O B) = some (cfgQ 0 (some true, none) R O B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q0_nil (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step progQ (cfgQ 0 v [] O B) = some (cfgQ 2 (none, none) [] O B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q1_some (a : Bool) (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 1 v (a :: R) O B) = some (cfgQ 1 (some a, none) R O B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q1_nil (v : Option Bool × Option Bool) (O B : List Bool) :
    TM2.step progQ (cfgQ 1 v [] O B) = some (cfgQ 3 (none, none) [] O B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q2 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 2 v R O B) = some (cfgQ 4 v R (true :: O) B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q3 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 3 v R O B) = some (cfgQ 4 v R (false :: O) B) := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

theorem q4 (v : Option Bool × Option Bool) (R O B : List Bool) :
    TM2.step progQ (cfgQ 4 v R O B) = some ⟨none, (none, none), ![R, O, B]⟩ := by
  simp [TM2.step, TM2.stepAux, progQ, cfgQ] <;> (funext k; fin_cases k <;> simp)

/-- Iterated machine steps, starting from a configuration. -/
def rn (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)) :=
  (fun o => o.bind (TM2.step progQ))^[n] (some c)

theorem rn_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
    (h : TM2.step progQ c = some c') : rn (n + 1) c = rn n c' := by
  unfold rn
  rw [Function.iterate_succ_apply]
  simp [h]

theorem rn_add {m n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 5) (Option Bool × Option Bool)}
    (h : rn m c = some c') : rn (n + m) c = rn n c' := by
  unfold rn at h ⊢
  rw [Function.iterate_add_apply, h]

/-- Draining phase: label 1 reads the rest of the input and reaches label 3 with it empty. -/
theorem drain : ∀ (y : List Bool) (v : Option Bool × Option Bool) (O B : List Bool),
    rn (y.length + 1) (cfgQ 1 v y O B) = some (cfgQ 3 (none, none) [] O B)
  | [], v, O, B => by
      rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rn_succ_step (q1_nil v O B)]
      simp [rn]
  | a :: y, v, O, B => by
      rw [show (a :: y).length + 1 = (y.length + 1) + 1 from rfl, rn_succ_step (q1_some a v y O B)]
      exact drain y (some a, none) O B

/-- The no-false test: from label 0 the machine halts with the answer on the output, in at most
`|y| + 3` steps. -/
theorem run : ∀ (y : List Bool) (v : Option Bool × Option Bool), ∃ n, n ≤ y.length + 3 ∧
    rn n (cfgQ 0 v y [] []) = some ⟨none, (none, none), ![[], [qf y], []]⟩
  | [], v => ⟨3, by simp, by
      show rn (2 + 1) (cfgQ 0 v [] [] []) = _
      rw [rn_succ_step (q0_nil v [] [])]
      show rn (1 + 1) _ = _
      rw [rn_succ_step (q2 _ [] [] [])]
      show rn (0 + 1) _ = _
      rw [rn_succ_step (q4 _ _ _ _)]
      simp [rn, qf]⟩
  | true :: y, v => by
      obtain ⟨n, hn, h⟩ := run y (some true, none)
      refine ⟨n + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [rn_succ_step (q0_true v y [] [])]
      rw [h]
      simp [qf]
  | false :: y, v => by
      refine ⟨(y.length + 1) + 3, by simp only [List.length_cons]; omega, ?_⟩
      rw [show y.length + 1 + 3 = (2 + (y.length + 1)) + 1 from by omega]
      show rn ((2 + (y.length + 1)) + 1) (cfgQ 0 v (false :: y) [] []) = _
      rw [rn_succ_step (q0_false v y [] []), rn_add (n := 2) (drain y (some false, none) [] [])]
      show rn (1 + 1) _ = _
      rw [rn_succ_step (q3 _ [] [] [])]
      show rn (0 + 1) _ = _
      rw [rn_succ_step (q4 _ _ _ _)]
      simp [rn, qf]

theorem initList_eq (z : List Bool) : initList tmQ z = cfgQ 0 (none, none) z [] [] := by
  unfold initList cfgQ
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tmQ]

theorem haltList_eq (O : List Bool) :
    haltList tmQ O = ⟨none, (none, none), ![[], O, []]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 3) => ?_
  fin_cases k <;> simp [tmQ]

noncomputable def machineQ :
    TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool qf where
  tm := tmQ
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 3
  outputsFun z := by
    have hs := (run z (none, none)).choose_spec.1
    have he := (run z (none, none)).choose_spec.2
    have key : (fun o => o.bind (TM2.step progQ))^[(run z (none, none)).choose]
        (some (initList tmQ z)) = some (haltList tmQ (encodeBool (qf z))) := by
      rw [initList_eq, haltList_eq]
      exact he
    refine ⟨⟨(run z (none, none)).choose, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tmQ) (List.map_id z)
        | exact congrArg (fun l => some (haltList tmQ l)) (List.map_id (encodeBool (qf z)))
    · simp only [id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega

/-- The sliding-window test of pnp-116: the window map of pnp-115 followed by the no-false test. -/
theorem main : ∀ g : Lang, InP g → ∀ k : ℕ, InP (fun x : List Bool =>
    decide (∀ i < x.length, i + (k + 1) ≤ x.length → g ((x.drop i).take (k + 1)) = true)) := by
  intro g hg k
  obtain ⟨f, ⟨hf⟩, hfeq⟩ := MPP.Solutions.Pnp115.main g hg k
  obtain ⟨hQ⟩ : InP qf := ⟨machineQ⟩
  obtain ⟨hC⟩ := MPP.Solutions.Pnp006.main hf hQ
  have hfun : (fun x : List Bool => decide (∀ i < x.length, i + (k + 1) ≤ x.length →
      g ((x.drop i).take (k + 1)) = true)) = qf ∘ f := by
    funext x
    simp only [Function.comp, qf]
    rw [hfeq x]
    apply decide_eq_decide.mpr
    constructor
    · intro h hmem
      rw [List.mem_ofFn] at hmem
      obtain ⟨i, hi⟩ := hmem
      have hw := h i (by omega) (by omega)
      rw [hi] at hw
      exact Bool.false_ne_true hw
    · intro h i hi hik
      by_contra hne
      apply h
      rw [List.mem_ofFn]
      refine ⟨⟨i, by omega⟩, ?_⟩
      simp only
      cases hv : g ((x.drop i).take (k + 1)) with
      | false => rfl
      | true => exact absurd hv hne
  rw [hfun]
  exact ⟨hC⟩

end MPP.Solutions.Pnp116
