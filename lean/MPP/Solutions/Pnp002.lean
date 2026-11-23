import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006

namespace MPP.Solutions.Pnp002

open MPP.PvsNP Computability Turing Turing.TM2.Stmt StateTransition

/-- Reads pairs of equal bits and returns their common values. It stops at the first pair
of unequal bits (or at a lone last bit). -/
def decodePairs : List Bool → List Bool
  | a :: c :: rest => if a = c then a :: decodePairs rest else []
  | _ => []

theorem decodePairs_length : ∀ y : List Bool, (decodePairs y).length ≤ y.length
  | a :: c :: rest => by
    unfold decodePairs
    split
    · have := decodePairs_length rest
      simp only [List.length_cons]
      omega
    · simp
  | [] => by simp [decodePairs]
  | [_] => by simp [decodePairs]

theorem decodePairs_pair (x w : List Bool) :
    decodePairs ((x.flatMap fun b => [b, b]) ++ [false, true] ++ w) = x := by
  induction x with
  | nil => simp [decodePairs]
  | cons b x ih =>
    have h : (b :: x).flatMap (fun b => [b, b]) ++ [false, true] ++ w
        = b :: b :: (x.flatMap (fun b => [b, b]) ++ [false, true] ++ w) := by
      simp
    rw [h, decodePairs, if_pos rfl, ih]

/-- Three stacks as one function: input, output and a temporary stack. -/
def stk3 (l0 l1 l2 : List Bool) : Fin 3 → List Bool := ![l0, l1, l2]

/-- Label `0`: take two bits from the input. Equal bits are pushed on the temporary stack
and the machine stays in `0`. Otherwise it goes to `1`. -/
def scanS : Turing.TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  pop 0 (fun _ o => o)
    (branch (fun s => s.isSome)
      (pop 0 (fun s o => if o = s then s else none)
        (branch (fun s => s.isSome)
          (push 2 (fun s => s.getD false) (goto fun _ => 0))
          (goto fun _ => 1)))
      (goto fun _ => 1))

/-- Label `1`: empty the input stack, then go to `2`. -/
def clearS : Turing.TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  pop 0 (fun _ o => o)
    (branch (fun s => s.isSome) (goto fun _ => 1) (goto fun _ => 2))

/-- Label `2`: move the temporary stack onto the output stack, then halt. -/
def moveS : Turing.TM2.Stmt (fun _ : Fin 3 => Bool) (Fin 3) (Option Bool) :=
  pop 2 (fun _ o => o)
    (branch (fun s => s.isSome)
      (push 1 (fun s => s.getD false) (goto fun _ => 2))
      (load (fun _ => none) halt))

abbrev decMachine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m := ![scanS, clearS, moveS]

theorem init_eq (y : List Bool) :
    initList decMachine y = ⟨some 0, none, stk3 y [] []⟩ := by
  unfold initList
  congr 1
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem halt_eq (y : List Bool) :
    haltList decMachine y = ⟨none, none, stk3 [] y []⟩ := by
  unfold haltList
  congr 1
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_scan_eq (a c : Bool) (h : c = a) (rest out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 0, v, stk3 (a :: c :: rest) out acc⟩
      = some ⟨some 0, some a, stk3 rest out (a :: acc)⟩ := by
  subst h
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, scanS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_scan_neq (a c : Bool) (h : c ≠ a) (rest out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 0, v, stk3 (a :: c :: rest) out acc⟩
      = some ⟨some 1, none, stk3 rest out acc⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, scanS, stk3, h]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_scan_one (a : Bool) (out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 0, v, stk3 [a] out acc⟩
      = some ⟨some 1, none, stk3 [] out acc⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, scanS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_scan_nil (out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 0, v, stk3 [] out acc⟩
      = some ⟨some 1, none, stk3 [] out acc⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, scanS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_clear_some (b : Bool) (r out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 1, v, stk3 (b :: r) out acc⟩
      = some ⟨some 1, some b, stk3 r out acc⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, clearS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_clear_nil (out acc : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 1, v, stk3 [] out acc⟩
      = some ⟨some 2, none, stk3 [] out acc⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, clearS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_move_some (h : Bool) (l out : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 2, v, stk3 [] out (h :: l)⟩
      = some ⟨some 2, some h, stk3 [] (h :: out) l⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, moveS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

theorem step_move_nil (out : List Bool) (v : Option Bool) :
    decMachine.step ⟨some 2, v, stk3 [] out []⟩
      = some ⟨none, none, stk3 [] out []⟩ := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, decMachine, moveS, stk3]
  congr 2
  all_goals first | rfl | (funext k; fin_cases k <;> rfl)

/-! ### Running the machine -/

def ev_one {a b : decMachine.Cfg} (h : decMachine.step a = some b) :
    EvalsToInTime decMachine.step a (some b) 1 :=
  ⟨⟨1, by rw [Function.iterate_one]; exact h⟩, le_refl 1⟩

def ev_mono {a : decMachine.Cfg} {b : Option decMachine.Cfg} {m m' : ℕ}
    (h : EvalsToInTime decMachine.step a b m) (hm : m ≤ m') :
    EvalsToInTime decMachine.step a b m' :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

def ev_trans {a b c : decMachine.Cfg} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime decMachine.step a (some b) m₁)
    (h₂ : EvalsToInTime decMachine.step b (some c) m₂) :
    EvalsToInTime decMachine.step a (some c) (m₂ + m₁) :=
  EvalsToInTime.trans decMachine.step m₁ m₂ a b (some c) h₁ h₂

def clear_run : ∀ (r out acc : List Bool) (v : Option Bool),
    EvalsToInTime decMachine.step ⟨some 1, v, stk3 r out acc⟩
      (some ⟨some 2, none, stk3 [] out acc⟩) (r.length + 1)
  | [], out, acc, v => ev_mono (ev_one (step_clear_nil out acc v)) (by simp)
  | b :: r, out, acc, v =>
    ev_mono (ev_trans (ev_one (step_clear_some b r out acc v)) (clear_run r out acc (some b)))
      (by simp)

def scan_run : ∀ (y out acc : List Bool) (v : Option Bool),
    EvalsToInTime decMachine.step ⟨some 0, v, stk3 y out acc⟩
      (some ⟨some 2, none, stk3 [] out ((decodePairs y).reverse ++ acc)⟩) (y.length + 2)
  | [], out, acc, v => by
    have h := ev_trans (ev_one (step_scan_nil out acc v)) (clear_run [] out acc none)
    have e : (decodePairs []).reverse ++ acc = acc := by simp [decodePairs]
    rw [e]
    exact ev_mono h (by simp)
  | [a], out, acc, v => by
    have h := ev_trans (ev_one (step_scan_one a out acc v)) (clear_run [] out acc none)
    have e : (decodePairs [a]).reverse ++ acc = acc := by simp [decodePairs]
    rw [e]
    exact ev_mono h (by simp)
  | a :: c :: rest, out, acc, v => by
    by_cases hc : c = a
    · have h := ev_trans (ev_one (step_scan_eq a c hc rest out acc v))
        (scan_run rest out (a :: acc) (some a))
      have e : (decodePairs (a :: c :: rest)).reverse ++ acc
          = (decodePairs rest).reverse ++ (a :: acc) := by
        simp [decodePairs, hc]
      rw [e]
      exact ev_mono h (by simp only [List.length_cons]; omega)
    · have h := ev_trans (ev_one (step_scan_neq a c hc rest out acc v))
        (clear_run rest out acc none)
      have hc' : a ≠ c := fun h' => hc h'.symm
      have e : (decodePairs (a :: c :: rest)).reverse ++ acc = acc := by
        simp [decodePairs, hc']
      rw [e]
      exact ev_mono h (by simp only [List.length_cons]; omega)

def move_run : ∀ (l out : List Bool) (v : Option Bool),
    EvalsToInTime decMachine.step ⟨some 2, v, stk3 [] out l⟩
      (some ⟨none, none, stk3 [] (l.reverse ++ out) []⟩) (l.length + 1)
  | [], out, v => by
    have h := ev_one (step_move_nil out v)
    simp only [List.reverse_nil, List.nil_append]
    exact ev_mono h (by simp)
  | x :: l, out, v => by
    have h1 := ev_one (step_move_some x l out v)
    have h2 := move_run l (x :: out) (some x)
    have e : (x :: l).reverse ++ out = l.reverse ++ (x :: out) := by simp
    rw [e]
    exact ev_mono (ev_trans h1 h2) (by simp only [List.length_cons]; omega)

def dec_run (y : List Bool) :
    EvalsToInTime decMachine.step (initList decMachine y)
      (some (haltList decMachine (decodePairs y))) (2 * y.length + 3) := by
  rw [init_eq, halt_eq]
  have hs := scan_run y [] [] none
  simp only [List.append_nil] at hs
  have hm := move_run (decodePairs y).reverse [] none
  have h := ev_trans hs hm
  have e : (decodePairs y).reverse.reverse ++ [] = decodePairs y := by simp
  rw [e] at h
  have hl := decodePairs_length y
  exact ev_mono h (by simp only [List.length_reverse]; omega)

/-- The decoder is computed in linear time by `decMachine`. -/
noncomputable def decComputable :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
      decodePairs where
  tm := decMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun := fun y => by
    have hy : List.map (Equiv.refl Bool).invFun (id y) = y := by simp
    have hd : List.map (Equiv.refl Bool).invFun (id (decodePairs y)) = decodePairs y := by
      simp
    have hb : (2 * Polynomial.X + 3 : Polynomial ℕ).eval (id y).length = 2 * y.length + 3 := by
      simp
    rw [hy, hd, hb]
    exact dec_run y

/-- If `L` is in P, then `L` is in NP: the verifier decodes the input from the pair
encoding and ignores the witness. -/
theorem main : ∀ L : Lang, InP L → InNP L := by
  intro L hL
  obtain ⟨hL'⟩ := hL
  have hV : InP (fun y => L (decodePairs y)) := MPP.Solutions.Pnp006.main decComputable hL'
  refine ⟨fun y => L (decodePairs y), hV, 0, ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    have h := decodePairs_pair x []
    simp only [List.append_nil] at h
    simp only [pair, List.append_nil]
    rw [h]
    exact hx
  · rintro ⟨w, -, hw⟩
    have h := decodePairs_pair x w
    simp only [pair] at hw
    rw [h] at hw
    exact hw

end MPP.Solutions.Pnp002
