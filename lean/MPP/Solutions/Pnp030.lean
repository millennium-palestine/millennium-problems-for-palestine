import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006
import MPP.Solutions.Pnp026
import MPP.Solutions.Pnp031

namespace MPP.Solutions.Pnp030

open MPP.PvsNP Computability Turing

/-! Two fixed machines, used for the base case and the step of the induction on `c`.
`empty` writes nothing; `one` writes `[false]`. Both empty the input first. -/

/-- Program of the machine that writes nothing: it pops the input until it is empty and halts. -/
def progE : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)
  | 0 => .pop 0 (fun _ h => h) (.branch (fun s => s.isSome) (.goto fun _ => 0) .halt)

def tmE : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 1
  main := 0
  σ := Option Bool
  initialState := none
  m := progE

/-- Program of the machine that writes `[false]`: it pops the input until it is empty, then
pushes `false` onto the output and halts. Label 0 drains, label 1 writes. -/
def progO : Fin 2 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)
  | 0 => .pop 0 (fun _ h => h) (.branch (fun s => s.isSome) (.goto fun _ => 0) (.goto fun _ => 1))
  | 1 => .push 1 (fun _ => false) .halt

def tmO : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ := fun _ => Bool
  Λ := Fin 2
  main := 0
  σ := Option Bool
  initialState := none
  m := progO

def cfgE (v : Option Bool) (R O : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool) :=
  ⟨some 0, v, ![R, O]⟩

theorem stepE_some (a : Bool) (v : Option Bool) (R O : List Bool) :
    TM2.step progE (cfgE v (a :: R) O) = some (cfgE (some a) R O) := by
  simp [TM2.step, TM2.stepAux, progE, cfgE] <;> (funext k; fin_cases k <;> simp)

theorem stepE_none (v : Option Bool) (O : List Bool) :
    TM2.step progE (cfgE v [] O) = some ⟨none, none, ![[], O]⟩ := by
  simp [TM2.step, TM2.stepAux, progE, cfgE] <;> (funext k; fin_cases k <;> simp)

def rnE (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) :=
  (fun o => o.bind (TM2.step progE))^[n] (some c)

theorem rnE_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)}
    (h : TM2.step progE c = some c') : rnE (n + 1) c = rnE n c' := by
  unfold rnE
  rw [Function.iterate_succ_apply]
  simp [h]

theorem runE (R O : List Bool) (v : Option Bool) :
    rnE (R.length + 1) (cfgE v R O) = some ⟨none, none, ![[], O]⟩ := by
  induction R generalizing v with
  | nil =>
    rw [show ([] : List Bool).length + 1 = 0 + 1 from rfl, rnE_succ_step (stepE_none v O)]
    simp [rnE]
  | cons a R ih =>
    rw [show (a :: R).length + 1 = (R.length + 1) + 1 from rfl, rnE_succ_step (stepE_some a v R O)]
    exact ih _

def cfgO (l : Fin 2) (v : Option Bool) (R O : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool) :=
  ⟨some l, v, ![R, O]⟩

theorem stepO_some (a : Bool) (v : Option Bool) (R O : List Bool) :
    TM2.step progO (cfgO 0 v (a :: R) O) = some (cfgO 0 (some a) R O) := by
  simp [TM2.step, TM2.stepAux, progO, cfgO] <;> (funext k; fin_cases k <;> simp)

theorem stepO_none (v : Option Bool) (O : List Bool) :
    TM2.step progO (cfgO 0 v [] O) = some (cfgO 1 none [] O) := by
  simp [TM2.step, TM2.stepAux, progO, cfgO] <;> (funext k; fin_cases k <;> simp)

theorem stepO_write (O : List Bool) :
    TM2.step progO (cfgO 1 none [] O) = some ⟨none, none, ![[], false :: O]⟩ := by
  simp [TM2.step, TM2.stepAux, progO, cfgO] <;> (funext k; fin_cases k <;> simp)

def rnO (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)) :
    Option (TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)) :=
  (fun o => o.bind (TM2.step progO))^[n] (some c)

theorem rnO_succ_step {n : ℕ}
    {c c' : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 2) (Option Bool)}
    (h : TM2.step progO c = some c') : rnO (n + 1) c = rnO n c' := by
  unfold rnO
  rw [Function.iterate_succ_apply]
  simp [h]

theorem runO (R O : List Bool) (v : Option Bool) :
    rnO (R.length + 2) (cfgO 0 v R O) = some ⟨none, none, ![[], false :: O]⟩ := by
  induction R generalizing v with
  | nil =>
    rw [show ([] : List Bool).length + 2 = (0 + 1) + 1 from rfl,
      rnO_succ_step (stepO_none v O)]
    rw [rnO_succ_step (stepO_write O)]
    simp [rnO]
  | cons a R ih =>
    rw [show (a :: R).length + 2 = (R.length + 2) + 1 from rfl, rnO_succ_step (stepO_some a v R O)]
    exact ih _

theorem initListE_eq (z : List Bool) : initList tmE z = cfgE none z [] := by
  unfold initList cfgE
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tmE]

theorem haltListE_eq (O : List Bool) : haltList tmE O = ⟨none, none, ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tmE]

theorem initListO_eq (z : List Bool) : initList tmO z = cfgO 0 none z [] := by
  unfold initList cfgO
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tmO]

theorem haltListO_eq (O : List Bool) : haltList tmO O = ⟨none, none, ![[], O]⟩ := by
  unfold haltList
  congr 1
  refine funext fun (k : Fin 2) => ?_
  fin_cases k <;> simp [tmO]

/-- The machine writing nothing, as a polynomial-time map. -/
noncomputable def machineE : TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
    (fun _ => ([] : List Bool)) where
  tm := tmE
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun x := by
    have key : (fun o => o.bind (TM2.step progE))^[x.length + 1] (some (initList tmE x)) =
        some (haltList tmE []) := by
      rw [initListE_eq, haltListE_eq]
      exact runE x [] none
    refine ⟨⟨x.length + 1, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tmE) (List.map_id x)
        | exact congrArg (fun l => some (haltList tmE l)) (List.map_id [])
    · simp

/-- The machine writing `[false]`, as a polynomial-time map. -/
noncomputable def machineO : TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool)
    (fun _ => [false]) where
  tm := tmO
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun x := by
    have key : (fun o => o.bind (TM2.step progO))^[x.length + 2] (some (initList tmO x)) =
        some (haltList tmO [false]) := by
      rw [initListO_eq, haltListO_eq]
      exact runO x [] none
    refine ⟨⟨x.length + 2, ?_⟩, ?_⟩
    · convert key using 3 <;> first
        | rfl
        | exact congrArg (initList tmO) (List.map_id x)
        | exact congrArg (fun l => some (haltList tmO l)) (List.map_id [false])
    · simp

theorem main : ∀ c : ℕ, ∃ g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) ∧
    ∀ x : List Bool, g x = List.replicate c false
  | 0 => ⟨fun _ => [], ⟨machineE⟩, fun _ => rfl⟩
  | c + 1 => by
    obtain ⟨g, ⟨hg⟩, hgx⟩ := main c
    obtain ⟨E, ⟨hE⟩, hEp⟩ := MPP.Solutions.Pnp031.main
    obtain ⟨h, ⟨hh⟩, hhz⟩ := MPP.Solutions.Pnp026.main g (fun _ => [false]) ⟨hg⟩ ⟨machineO⟩
    obtain ⟨k⟩ := MPP.Solutions.Pnp006.main hh hE
    refine ⟨fun x => E (h x), ⟨k⟩, fun x => ?_⟩
    dsimp only
    rw [hhz x, hEp, hgx x]
    simp [Nat.add_comm]

end MPP.Solutions.Pnp030
