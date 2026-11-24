import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp009

open MPP.PvsNP Turing


section Defs

variable (MA MB : TM2ComputableAux Bool Bool)

/-- Stacks of the tupling machine: three Boolean stacks (input, buffer, output),
then the stacks of `MA` and of `MB`. -/
abbrev TK := Fin 3 ⊕ (MA.tm.K ⊕ MB.tm.K)

/-- Alphabets: Booleans on the three private stacks, then the alphabets of `MA` and `MB`. -/
def TG : TK MA MB → Type :=
  Sum.elim (fun _ => Bool) (Sum.elim MA.tm.Γ MB.tm.Γ)

/-- Control labels. -/
inductive Ctl
  | p1 | p2 | afterA | afterB

def ctlDecEq : DecidableEq Ctl := fun x y => by
  cases x <;> cases y <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)

def ctlFintype : Fintype Ctl := by
  haveI := ctlDecEq
  exact Fintype.ofList [Ctl.p1, Ctl.p2, Ctl.afterA, Ctl.afterB] (by intro x; cases x <;> simp)

/-- Labels: control labels, then the labels of `MA` and `MB`. -/
abbrev TL := Ctl ⊕ (MA.tm.Λ ⊕ MB.tm.Λ)

/-- States: the state of `MA`, the state of `MB`, and two Boolean registers. -/
abbrev TS := MA.tm.σ × MB.tm.σ × Option Bool × Option Bool

/-- Lifting of a statement of `MA` onto the stacks, labels and states of the tupling machine. -/
def liftA : TM2.Stmt MA.tm.Γ MA.tm.Λ MA.tm.σ → TM2.Stmt (TG MA MB) (TL MA MB) (TS MA MB)
  | .push k f q => .push (Sum.inr (Sum.inl k)) (fun s => f s.1) (liftA q)
  | .peek k f q => .peek (Sum.inr (Sum.inl k)) (fun s x => (f s.1 x, s.2.1, s.2.2)) (liftA q)
  | .pop k f q => .pop (Sum.inr (Sum.inl k)) (fun s x => (f s.1 x, s.2.1, s.2.2)) (liftA q)
  | .load a q => .load (fun s => (a s.1, s.2)) (liftA q)
  | .branch p q₁ q₂ => .branch (fun s => p s.1) (liftA q₁) (liftA q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.1)))
  | .halt => .goto (fun _ => Sum.inl Ctl.afterA)

/-- Lifting of a statement of `MB` onto the stacks, labels and states of the tupling machine. -/
def liftB : TM2.Stmt MB.tm.Γ MB.tm.Λ MB.tm.σ → TM2.Stmt (TG MA MB) (TL MA MB) (TS MA MB)
  | .push k f q => .push (Sum.inr (Sum.inr k)) (fun s => f s.2.1) (liftB q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) (fun s x => (s.1, f s.2.1 x, s.2.2)) (liftB q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) (fun s x => (s.1, f s.2.1 x, s.2.2)) (liftB q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (liftB q)
  | .branch p q₁ q₂ => .branch (fun s => p s.2.1) (liftB q₁) (liftB q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inr (f s.2.1)))
  | .halt => .goto (fun _ => Sum.inl Ctl.afterB)

/-- The three-phase control: copy the input, run `MA`, run `MB`, write the two bits. -/
def ctlStmt : Ctl → TM2.Stmt (TG MA MB) (TL MA MB) (TS MA MB)
  | .p1 =>
    .pop (Sum.inl 0) (fun s x => (s.1, s.2.1, x, s.2.2.2))
      (.branch (fun s => s.2.2.1.isNone)
        (.goto (fun _ => Sum.inl Ctl.p2))
        (.push (Sum.inl 1) (fun s => s.2.2.1.getD false)
          (.goto (fun _ => Sum.inl Ctl.p1))))
  | .p2 =>
    .pop (Sum.inl 1) (fun s x => (s.1, s.2.1, x, s.2.2.2))
      (.branch (fun s => s.2.2.1.isNone)
        (.goto (fun _ => Sum.inr (Sum.inl MA.tm.main)))
        (.push (Sum.inr (Sum.inl MA.tm.k₀)) (fun s => MA.inputAlphabet.invFun (s.2.2.1.getD false))
          (.push (Sum.inr (Sum.inr MB.tm.k₀)) (fun s => MB.inputAlphabet.invFun (s.2.2.1.getD false))
            (.goto (fun _ => Sum.inl Ctl.p2)))))
  | .afterA =>
    .pop (Sum.inr (Sum.inl MA.tm.k₁)) (fun s x => (s.1, s.2.1, s.2.2.1, x.map MA.outputAlphabet))
      (.goto (fun _ => Sum.inr (Sum.inr MB.tm.main)))
  | .afterB =>
    .pop (Sum.inr (Sum.inr MB.tm.k₁)) (fun s x => (s.1, s.2.1, x.map MB.outputAlphabet, s.2.2.2))
      (.push (Sum.inl 2) (fun s => s.2.2.1.getD false)
        (.push (Sum.inl 2) (fun s => s.2.2.2.getD false)
          (.load (fun _ => (MA.tm.initialState, MB.tm.initialState, none, none)) .halt)))

/-- The tupling machine. -/
def tm_m : TL MA MB → TM2.Stmt (TG MA MB) (TL MA MB) (TS MA MB)
  | Sum.inl c => ctlStmt MA MB c
  | Sum.inr (Sum.inl l) => liftA MA MB (MA.tm.m l)
  | Sum.inr (Sum.inr l) => liftB MA MB (MB.tm.m l)

/-- The tupling machine, with input and output on the first Boolean stack. -/
noncomputable abbrev TupTM : FinTM2 where
  K := TK MA MB
  k₀ := Sum.inl 0
  k₁ := Sum.inl 2
  Γ := TG MA MB
  Λ := TL MA MB
  main := Sum.inl Ctl.p1
  σ := TS MA MB
  initialState := (MA.tm.initialState, MB.tm.initialState, none, none)
  m := tm_m MA MB
  kFin := by
    haveI := MA.tm.kFin
    haveI := MB.tm.kFin
    infer_instance
  ΛFin := by
    haveI := ctlFintype
    haveI := MA.tm.ΛFin
    haveI := MB.tm.ΛFin
    infer_instance
  σFin := by
    haveI := MA.tm.σFin
    haveI := MB.tm.σFin
    infer_instance
  Γk₀Fin := inferInstanceAs (Fintype Bool)

/-- A label of `MA` (or `none`, meaning halt) as a label of the tupling machine. -/
def labA : Option MA.tm.Λ → Option (TL MA MB)
  | none => some (Sum.inl Ctl.afterA)
  | some l => some (Sum.inr (Sum.inl l))

/-- A label of `MB` (or `none`, meaning halt) as a label of the tupling machine. -/
def labB : Option MB.tm.Λ → Option (TL MA MB)
  | none => some (Sum.inl Ctl.afterB)
  | some l => some (Sum.inr (Sum.inr l))

theorem stepA_spec (q : TM2.Stmt MA.tm.Γ MA.tm.Λ MA.tm.σ) :
    ∀ (s : TS MA MB) (S : ∀ k, List (TG MA MB k)) (T0 : ∀ k, List (MA.tm.Γ k)),
      (∀ k, S (Sum.inr (Sum.inl k)) = T0 k) →
      (TM2.stepAux (liftA MA MB q) s S).l = labA MA MB (TM2.stepAux q s.1 T0).l ∧
      (TM2.stepAux (liftA MA MB q) s S).var = ((TM2.stepAux q s.1 T0).var, s.2) ∧
      (∀ k, (TM2.stepAux (liftA MA MB q) s S).stk (Sum.inr (Sum.inl k)) =
        (TM2.stepAux q s.1 T0).stk k) ∧
      (∀ kt, (∀ k, kt ≠ Sum.inr (Sum.inl k)) →
        (TM2.stepAux (liftA MA MB q) s S).stk kt = S kt) := by
  induction q with
  | push k f q ih =>
    intro s S T0 hS
    have hS' : ∀ k', Function.update S (Sum.inr (Sum.inl k)) (f s.1 :: S (Sum.inr (Sum.inl k)))
        (Sum.inr (Sum.inl k')) = Function.update T0 k (f s.1 :: T0 k) k' := by
      intro k'
      by_cases h : k' = k
      · subst h
        rw [Function.update_self, Function.update_self]
        exact congrArg (fun l => f s.1 :: l) (hS k')
      · have hne1 : (Sum.inr (Sum.inl k') : TK MA MB) ≠ Sum.inr (Sum.inl k) := by simp [h]
        rw [Function.update_of_ne hne1, hS k', Function.update_of_ne h]
    obtain ⟨h1, h2, h3, h4⟩ := ih s _ _ hS'
    simp only [liftA, TM2.stepAux]
    refine ⟨h1, h2, ?_, ?_⟩
    · intro k'
      simpa [Function.update_apply] using h3 k'
    · intro kt hkt
      rw [h4 kt hkt]
      simp [Function.update_apply, hkt]
  | peek k f q ih =>
    intro s S T0 hS
    have hk : (S (Sum.inr (Sum.inl k))).head? = (T0 k).head? := congrArg List.head? (hS k)
    have := ih (f s.1 (T0 k).head?, s.2) S T0 hS
    simp only [liftA, TM2.stepAux]
    rw [hk]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  | pop k f q ih =>
    intro s S T0 hS
    have hk : (S (Sum.inr (Sum.inl k))).head? = (T0 k).head? := congrArg List.head? (hS k)
    have hS' : ∀ k', Function.update S (Sum.inr (Sum.inl k))
        (S (Sum.inr (Sum.inl k))).tail (Sum.inr (Sum.inl k')) =
          Function.update T0 k (T0 k).tail k' := by
      intro k'
      by_cases h : k' = k
      · subst h
        rw [Function.update_self, Function.update_self]
        exact congrArg List.tail (hS k')
      · have hne1 : (Sum.inr (Sum.inl k') : TK MA MB) ≠ Sum.inr (Sum.inl k) := by simp [h]
        rw [Function.update_of_ne hne1, hS k', Function.update_of_ne h]
    have := ih (f s.1 (T0 k).head?, s.2)
      (Function.update S (Sum.inr (Sum.inl k)) (S (Sum.inr (Sum.inl k))).tail)
      (Function.update T0 k (T0 k).tail) hS'
    simp only [liftA, TM2.stepAux]
    rw [hk]
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    intro kt hkt
    rw [this.2.2.2 kt hkt, Function.update_of_ne (hkt k)]
  | load a q ih =>
    intro s S T0 hS
    have := ih (a s.1, s.2) S T0 hS
    simp only [liftA, TM2.stepAux]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro s S T0 hS
    have h1 := ih₁ s S T0 hS
    have h2 := ih₂ s S T0 hS
    cases hb : p s.1
    · simp only [liftA, TM2.stepAux, hb, cond_false]
      exact h2
    · simp only [liftA, TM2.stepAux, hb, cond_true]
      exact h1
  | goto f =>
    intro s S T0 hS
    refine ⟨?_, ?_, fun k => hS k, fun kt _ => rfl⟩
    · simp [liftA, TM2.stepAux, labA]
    · simp [liftA, TM2.stepAux]
  | halt =>
    intro s S T0 hS
    refine ⟨?_, ?_, fun k => hS k, fun kt _ => rfl⟩
    · simp [liftA, TM2.stepAux, labA]
    · simp [liftA, TM2.stepAux]

theorem stepB_spec (q : TM2.Stmt MB.tm.Γ MB.tm.Λ MB.tm.σ) :
    ∀ (s : TS MA MB) (S : ∀ k, List (TG MA MB k)) (T0 : ∀ k, List (MB.tm.Γ k)),
      (∀ k, S (Sum.inr (Sum.inr k)) = T0 k) →
      (TM2.stepAux (liftB MA MB q) s S).l = labB MA MB (TM2.stepAux q s.2.1 T0).l ∧
      (TM2.stepAux (liftB MA MB q) s S).var = (s.1, (TM2.stepAux q s.2.1 T0).var, s.2.2) ∧
      (∀ k, (TM2.stepAux (liftB MA MB q) s S).stk (Sum.inr (Sum.inr k)) =
        (TM2.stepAux q s.2.1 T0).stk k) ∧
      (∀ kt, (∀ k, kt ≠ Sum.inr (Sum.inr k)) →
        (TM2.stepAux (liftB MA MB q) s S).stk kt = S kt) := by
  induction q with
  | push k f q ih =>
    intro s S T0 hS
    have hS' : ∀ k', Function.update S (Sum.inr (Sum.inr k)) (f s.2.1 :: S (Sum.inr (Sum.inr k)))
        (Sum.inr (Sum.inr k')) = Function.update T0 k (f s.2.1 :: T0 k) k' := by
      intro k'
      by_cases h : k' = k
      · subst h
        rw [Function.update_self, Function.update_self]
        exact congrArg (fun l => f s.2.1 :: l) (hS k')
      · have hne1 : (Sum.inr (Sum.inr k') : TK MA MB) ≠ Sum.inr (Sum.inr k) := by simp [h]
        rw [Function.update_of_ne hne1, hS k', Function.update_of_ne h]
    obtain ⟨h1, h2, h3, h4⟩ := ih s _ _ hS'
    simp only [liftB, TM2.stepAux]
    refine ⟨h1, h2, ?_, ?_⟩
    · intro k'
      simpa [Function.update_apply] using h3 k'
    · intro kt hkt
      rw [h4 kt hkt]
      simp [hkt]
  | peek k f q ih =>
    intro s S T0 hS
    have hk : (S (Sum.inr (Sum.inr k))).head? = (T0 k).head? := congrArg List.head? (hS k)
    have := ih (s.1, f s.2.1 (T0 k).head?, s.2.2) S T0 hS
    simp only [liftB, TM2.stepAux]
    rw [hk]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  | pop k f q ih =>
    intro s S T0 hS
    have hk : (S (Sum.inr (Sum.inr k))).head? = (T0 k).head? := congrArg List.head? (hS k)
    have hS' : ∀ k', Function.update S (Sum.inr (Sum.inr k))
        (S (Sum.inr (Sum.inr k))).tail (Sum.inr (Sum.inr k')) =
          Function.update T0 k (T0 k).tail k' := by
      intro k'
      by_cases h : k' = k
      · subst h
        rw [Function.update_self, Function.update_self]
        exact congrArg List.tail (hS k')
      · have hne1 : (Sum.inr (Sum.inr k') : TK MA MB) ≠ Sum.inr (Sum.inr k) := by simp [h]
        rw [Function.update_of_ne hne1, hS k', Function.update_of_ne h]
    have := ih (s.1, f s.2.1 (T0 k).head?, s.2.2)
      (Function.update S (Sum.inr (Sum.inr k)) (S (Sum.inr (Sum.inr k))).tail)
      (Function.update T0 k (T0 k).tail) hS'
    simp only [liftB, TM2.stepAux]
    rw [hk]
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    intro kt hkt
    rw [this.2.2.2 kt hkt, Function.update_of_ne (hkt k)]
  | load a q ih =>
    intro s S T0 hS
    have := ih (s.1, a s.2.1, s.2.2) S T0 hS
    simp only [liftB, TM2.stepAux]
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro s S T0 hS
    have h1 := ih₁ s S T0 hS
    have h2 := ih₂ s S T0 hS
    cases hb : p s.2.1
    · simp only [liftB, TM2.stepAux, hb, cond_false]
      exact h2
    · simp only [liftB, TM2.stepAux, hb, cond_true]
      exact h1
  | goto f =>
    intro s S T0 hS
    refine ⟨?_, ?_, fun k => hS k, fun kt _ => rfl⟩
    · simp [liftB, TM2.stepAux, labB]
    · simp [liftB, TM2.stepAux]
  | halt =>
    intro s S T0 hS
    refine ⟨?_, ?_, fun k => hS k, fun kt _ => rfl⟩
    · simp [liftB, TM2.stepAux, labB]
    · simp [liftB, TM2.stepAux]

/-- The tupling configuration `R` currently simulates the `MA`-configuration `c`. -/
abbrev RelA (c : MA.tm.Cfg) (R : (TupTM MA MB).Cfg) : Prop :=
  R.l = labA MA MB c.l ∧ R.var.1 = c.var ∧ ∀ k, R.stk (Sum.inr (Sum.inl k)) = c.stk k

/-- Running an `MA`-step leaves the `B`-part of the state and all non-`MA` stacks alone. -/
abbrev FrameA (R R' : (TupTM MA MB).Cfg) : Prop :=
  R'.var.2 = R.var.2 ∧ ∀ kt, (∀ k, kt ≠ Sum.inr (Sum.inl k)) → R'.stk kt = R.stk kt

theorem stepA_one (c c1 : MA.tm.Cfg) (R : (TupTM MA MB).Cfg) (l : MA.tm.Λ)
    (hc : c.l = some l) (h1 : MA.tm.step c = some c1) (hR : RelA MA MB c R) :
    ∃ R1, (TupTM MA MB).step R = some R1 ∧ RelA MA MB c1 R1 ∧ FrameA MA MB R R1 := by
  obtain ⟨cl, cv, cs⟩ := c
  obtain ⟨rl, rv, rs⟩ := R
  simp only at hc
  subst hc
  have hc1 : c1 = TM2.stepAux (MA.tm.m l) cv cs := by
    have h' : FinTM2.step MA.tm ⟨some l, cv, cs⟩ = some (TM2.stepAux (MA.tm.m l) cv cs) := rfl
    rw [h'] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨hRl, hRv, hRs⟩ := hR
  simp only [labA] at hRl
  simp only at hRv hRs
  subst hRl
  subst hc1
  have hT : (TupTM MA MB).step ⟨some (Sum.inr (Sum.inl l)), rv, rs⟩ =
      some (TM2.stepAux (liftA MA MB (MA.tm.m l)) rv rs) := rfl
  obtain ⟨hl, hv, hstk, hfr⟩ := stepA_spec MA MB (MA.tm.m l) rv rs cs hRs
  rw [hRv] at hl hv hstk
  have hv1 : (TM2.stepAux (liftA MA MB (MA.tm.m l)) rv rs).var.1 =
      (TM2.stepAux (MA.tm.m l) cv cs).var := congrArg Prod.fst hv
  have hv2 : (TM2.stepAux (liftA MA MB (MA.tm.m l)) rv rs).var.2 = rv.2 := by
    have h' := congrArg Prod.snd hv
    exact h'
  refine ⟨TM2.stepAux (liftA MA MB (MA.tm.m l)) rv rs, hT, ⟨hl, hv1, hstk⟩, ⟨hv2, hfr⟩⟩

theorem runA (n : ℕ) : ∀ (c c' : MA.tm.Cfg) (R : (TupTM MA MB).Cfg),
    (flip bind MA.tm.step)^[n] (some c) = some c' → RelA MA MB c R →
    ∃ R', (flip bind (TupTM MA MB).step)^[n] (some R) = some R' ∧ RelA MA MB c' R' ∧
      FrameA MA MB R R' := by
  induction n with
  | zero =>
    intro c c' R h hR
    have hcc : c = c' := Option.some.inj (by simpa using h)
    subst hcc
    exact ⟨R, rfl, hR, ⟨rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    intro c c' R h hR
    rcases c with ⟨cl, cv, cs⟩
    rw [Function.iterate_succ_apply] at h
    change (flip bind MA.tm.step)^[n] (MA.tm.step ⟨cl, cv, cs⟩) = some c' at h
    cases cl with
    | none =>
      have hstep : MA.tm.step ⟨none, cv, cs⟩ = none := rfl
      have hfix : (flip bind MA.tm.step)^[n] none = none := Function.iterate_fixed rfl n
      rw [hstep, hfix] at h
      cases h
    | some l =>
      have hc1 : ∃ c1, MA.tm.step ⟨some l, cv, cs⟩ = some c1 :=
        ⟨TM2.stepAux (MA.tm.m l) cv cs, rfl⟩
      obtain ⟨c1, hc1⟩ := hc1
      rw [hc1] at h
      obtain ⟨R1, hR1, hRel1, hfr1⟩ := stepA_one MA MB ⟨some l, cv, cs⟩ c1 R l rfl hc1 hR
      obtain ⟨R', hR', hRel', hfr'⟩ := ih c1 c' R1 h hRel1
      refine ⟨R', ?_, hRel', hfr'.1.trans hfr1.1, ?_⟩
      · rw [Function.iterate_succ_apply]
        change (flip bind (TupTM MA MB).step)^[n] ((TupTM MA MB).step R) = some R'
        rw [hR1]
        exact hR'
      · intro kt hk
        exact (hfr'.2 kt hk).trans (hfr1.2 kt hk)

/-- The tupling configuration `R` currently simulates the `MB`-configuration `c`. -/
abbrev RelB (c : MB.tm.Cfg) (R : (TupTM MA MB).Cfg) : Prop :=
  R.l = labB MA MB c.l ∧ R.var.2.1 = c.var ∧ ∀ k, R.stk (Sum.inr (Sum.inr k)) = c.stk k

/-- Running an `MB`-step leaves the `A`-part of the state, the registers and the non-`MB`
stacks alone. -/
abbrev FrameB (R R' : (TupTM MA MB).Cfg) : Prop :=
  R'.var.1 = R.var.1 ∧ R'.var.2.2 = R.var.2.2 ∧
    ∀ kt, (∀ k, kt ≠ Sum.inr (Sum.inr k)) → R'.stk kt = R.stk kt

theorem stepB_one (c c1 : MB.tm.Cfg) (R : (TupTM MA MB).Cfg) (l : MB.tm.Λ)
    (hc : c.l = some l) (h1 : MB.tm.step c = some c1) (hR : RelB MA MB c R) :
    ∃ R1, (TupTM MA MB).step R = some R1 ∧ RelB MA MB c1 R1 ∧ FrameB MA MB R R1 := by
  obtain ⟨cl, cv, cs⟩ := c
  obtain ⟨rl, rv, rs⟩ := R
  simp only at hc
  subst hc
  have hc1 : c1 = TM2.stepAux (MB.tm.m l) cv cs := by
    have h' : FinTM2.step MB.tm ⟨some l, cv, cs⟩ = some (TM2.stepAux (MB.tm.m l) cv cs) := rfl
    rw [h'] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨hRl, hRv, hRs⟩ := hR
  simp only [labB] at hRl
  simp only at hRv hRs
  subst hRl
  subst hc1
  have hT : (TupTM MA MB).step ⟨some (Sum.inr (Sum.inr l)), rv, rs⟩ =
      some (TM2.stepAux (liftB MA MB (MB.tm.m l)) rv rs) := rfl
  obtain ⟨hl, hv, hstk, hfr⟩ := stepB_spec MA MB (MB.tm.m l) rv rs cs hRs
  rw [hRv] at hl hv hstk
  have hv1 : (TM2.stepAux (liftB MA MB (MB.tm.m l)) rv rs).var.1 = rv.1 := by
    have h' := congrArg (fun x => x.1) hv
    exact h'
  have hv2 : (TM2.stepAux (liftB MA MB (MB.tm.m l)) rv rs).var.2.1 =
      (TM2.stepAux (MB.tm.m l) cv cs).var := by
    have h' := congrArg (fun x => x.2.1) hv
    exact h'
  have hv3 : (TM2.stepAux (liftB MA MB (MB.tm.m l)) rv rs).var.2.2 = rv.2.2 := by
    have h' := congrArg (fun x => x.2.2) hv
    exact h'
  refine ⟨TM2.stepAux (liftB MA MB (MB.tm.m l)) rv rs, hT, ⟨hl, hv2, hstk⟩, ⟨hv1, hv3, hfr⟩⟩

theorem runB (n : ℕ) : ∀ (c c' : MB.tm.Cfg) (R : (TupTM MA MB).Cfg),
    (flip bind MB.tm.step)^[n] (some c) = some c' → RelB MA MB c R →
    ∃ R', (flip bind (TupTM MA MB).step)^[n] (some R) = some R' ∧ RelB MA MB c' R' ∧
      FrameB MA MB R R' := by
  induction n with
  | zero =>
    intro c c' R h hR
    have hcc : c = c' := Option.some.inj (by simpa using h)
    subst hcc
    exact ⟨R, rfl, hR, ⟨rfl, rfl, fun _ _ => rfl⟩⟩
  | succ n ih =>
    intro c c' R h hR
    rcases c with ⟨cl, cv, cs⟩
    rw [Function.iterate_succ_apply] at h
    change (flip bind MB.tm.step)^[n] (MB.tm.step ⟨cl, cv, cs⟩) = some c' at h
    cases cl with
    | none =>
      have hstep : MB.tm.step ⟨none, cv, cs⟩ = none := rfl
      have hfix : (flip bind MB.tm.step)^[n] none = none := Function.iterate_fixed rfl n
      rw [hstep, hfix] at h
      cases h
    | some l =>
      have hc1 : ∃ c1, MB.tm.step ⟨some l, cv, cs⟩ = some c1 :=
        ⟨TM2.stepAux (MB.tm.m l) cv cs, rfl⟩
      obtain ⟨c1, hc1⟩ := hc1
      rw [hc1] at h
      obtain ⟨R1, hR1, hRel1, hfr1⟩ := stepB_one MA MB ⟨some l, cv, cs⟩ c1 R l rfl hc1 hR
      obtain ⟨R', hR', hRel', hfr'⟩ := ih c1 c' R1 h hRel1
      refine ⟨R', ?_, hRel', hfr'.1.trans hfr1.1, hfr'.2.1.trans hfr1.2.1, ?_⟩
      · rw [Function.iterate_succ_apply]
        change (flip bind (TupTM MA MB).step)^[n] ((TupTM MA MB).step R) = some R'
        rw [hR1]
        exact hR'
      · intro kt hk
        exact (hfr'.2.2 kt hk).trans (hfr1.2.2 kt hk)

theorem initList_stk_self' (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk tm.k₀ = s := by
  simp [initList]

theorem initList_stk_ne' (tm : FinTM2) (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := by
  simp [initList, h]

theorem p1_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (h : S (Sum.inl 0) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.p1) v S =
      { l := some (Sum.inl Ctl.p2), var := (v.1, v.2.1, none, v.2.2.2),
        stk := Function.update S (Sum.inl 0) [] } := by
  simp only [ctlStmt, TM2.stepAux, h]
  rfl

theorem p1_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (a : Bool) (l : List Bool)
    (h : S (Sum.inl 0) = a :: l) :
    TM2.stepAux (ctlStmt MA MB Ctl.p1) v S =
      { l := some (Sum.inl Ctl.p1), var := (v.1, v.2.1, some a, v.2.2.2),
        stk := Function.update (Function.update S (Sum.inl 0) l) (Sum.inl 1)
          (a :: S (Sum.inl 1)) } := by
  simp only [ctlStmt, TM2.stepAux, h]
  rfl

theorem p2_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (h : S (Sum.inl 1) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.p2) v S =
      { l := some (Sum.inr (Sum.inl MA.tm.main)), var := (v.1, v.2.1, none, v.2.2.2),
        stk := Function.update S (Sum.inl 1) [] } := by
  simp only [ctlStmt, TM2.stepAux, h]
  rfl

theorem p2_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (b : Bool) (r : List Bool)
    (h : S (Sum.inl 1) = b :: r) :
    TM2.stepAux (ctlStmt MA MB Ctl.p2) v S =
      { l := some (Sum.inl Ctl.p2), var := (v.1, v.2.1, some b, v.2.2.2),
        stk := Function.update (Function.update (Function.update S (Sum.inl 1) r)
          (Sum.inr (Sum.inl MA.tm.k₀))
          (MA.inputAlphabet.invFun b :: S (Sum.inr (Sum.inl MA.tm.k₀))))
          (Sum.inr (Sum.inr MB.tm.k₀))
          (MB.inputAlphabet.invFun b :: S (Sum.inr (Sum.inr MB.tm.k₀))) } := by
  simp only [ctlStmt, TM2.stepAux, h]
  rfl

/-- One step of `p1` on a configuration with label `p1`. -/
theorem step_p1 (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.p1)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.p1) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

theorem step_p2 (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.p2)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.p2) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

/-- Pass 1 of the copy: move the input stack onto the buffer, reversing it. -/
theorem pass1 (l r : List Bool) : ∀ (C : (TupTM MA MB).Cfg),
    C.l = some (Sum.inl Ctl.p1) → C.stk (Sum.inl 0) = l → C.stk (Sum.inl 1) = r →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[l.length + 1] (some C) = some C' ∧
      C'.l = some (Sum.inl Ctl.p2) ∧ C'.var = (C.var.1, C.var.2.1, none, C.var.2.2.2) ∧
      C'.stk (Sum.inl 0) = [] ∧ C'.stk (Sum.inl 1) = l.reverse ++ r ∧
      ∀ kt, kt ≠ Sum.inl 0 → kt ≠ Sum.inl 1 → C'.stk kt = C.stk kt := by
  induction l generalizing r with
  | nil =>
    intro C hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hne : (Sum.inl 1 : TK MA MB) ≠ Sum.inl 0 := by simp
    refine ⟨⟨some (Sum.inl Ctl.p2), (cv.1, cv.2.1, none, cv.2.2.2),
      Function.update cs (Sum.inl 0) []⟩, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · show (TupTM MA MB).step ⟨some (Sum.inl Ctl.p1), cv, cs⟩ = _
      rw [step_p1 MA MB ⟨some (Sum.inl Ctl.p1), cv, cs⟩ rfl, p1_nil MA MB cv cs h0]
      rfl
    · simp
    · dsimp only
      rw [Function.update_of_ne hne]
      simp [h1]
    · intro kt hk0 _
      dsimp only
      rw [Function.update_of_ne hk0]
  | cons a l ih =>
    intro C hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hne : (Sum.inl 0 : TK MA MB) ≠ Sum.inl 1 := by simp
    have hC1 : (TupTM MA MB).step ⟨some (Sum.inl Ctl.p1), cv, cs⟩ =
        some ⟨some (Sum.inl Ctl.p1), (cv.1, cv.2.1, some a, cv.2.2.2),
          Function.update (Function.update cs (Sum.inl 0) l) (Sum.inl 1)
            (a :: cs (Sum.inl 1))⟩ := by
      rw [step_p1 MA MB ⟨some (Sum.inl Ctl.p1), cv, cs⟩ rfl, p1_cons MA MB cv cs a l h0]
      rfl
    have hI0 : Function.update (Function.update cs (Sum.inl 0) l) (Sum.inl 1)
        (a :: cs (Sum.inl 1)) (Sum.inl 0) = l := by
      rw [Function.update_of_ne hne, Function.update_self]
    have hI1 : Function.update (Function.update cs (Sum.inl 0) l) (Sum.inl 1)
        (a :: cs (Sum.inl 1)) (Sum.inl 1) = a :: r := by
      rw [Function.update_self, h1]
      rfl
    obtain ⟨C', hC', hl', hv', hs0', hs1', hfr'⟩ := ih (r := a :: r)
      ⟨some (Sum.inl Ctl.p1), (cv.1, cv.2.1, some a, cv.2.2.2),
        Function.update (Function.update cs (Sum.inl 0) l) (Sum.inl 1) (a :: cs (Sum.inl 1))⟩
      rfl hI0 hI1
    refine ⟨C', ?_, hl', hv', hs0', ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind (TupTM MA MB).step)^[l.length + 1]
        ((TupTM MA MB).step ⟨some (Sum.inl Ctl.p1), cv, cs⟩) = some C'
      rw [hC1]
      exact hC'
    · dsimp only
      rw [hs1']
      simp [List.reverse_cons, List.append_assoc]
    · intro kt hk0 hk1
      dsimp only
      rw [hfr' kt hk0 hk1]
      dsimp only
      rw [Function.update_of_ne hk1, Function.update_of_ne hk0]

/-- Pass 2 of the copy: move the buffer onto the two input stacks, restoring the order. -/
theorem pass2 (r : List Bool) : ∀ (C : (TupTM MA MB).Cfg),
    C.l = some (Sum.inl Ctl.p2) → C.stk (Sum.inl 1) = r →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[r.length + 1] (some C) = some C' ∧
      C'.l = some (Sum.inr (Sum.inl MA.tm.main)) ∧
      C'.var = (C.var.1, C.var.2.1, none, C.var.2.2.2) ∧
      C'.stk (Sum.inl 1) = [] ∧
      C'.stk (Sum.inr (Sum.inl MA.tm.k₀)) =
        (r.reverse.map MA.inputAlphabet.invFun : List (TG MA MB (Sum.inr (Sum.inl MA.tm.k₀)))) ++
          C.stk (Sum.inr (Sum.inl MA.tm.k₀)) ∧
      C'.stk (Sum.inr (Sum.inr MB.tm.k₀)) =
        (r.reverse.map MB.inputAlphabet.invFun : List (TG MA MB (Sum.inr (Sum.inr MB.tm.k₀)))) ++
          C.stk (Sum.inr (Sum.inr MB.tm.k₀)) ∧
      ∀ kt, kt ≠ Sum.inl 1 → kt ≠ Sum.inr (Sum.inl MA.tm.k₀) →
        kt ≠ Sum.inr (Sum.inr MB.tm.k₀) → C'.stk kt = C.stk kt := by
  induction r with
  | nil =>
    intro C hl h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h1
    subst hl
    have hA : (Sum.inr (Sum.inl MA.tm.k₀) : TK MA MB) ≠ Sum.inl 1 := by simp
    have hB : (Sum.inr (Sum.inr MB.tm.k₀) : TK MA MB) ≠ Sum.inl 1 := by simp
    refine ⟨⟨some (Sum.inr (Sum.inl MA.tm.main)), (cv.1, cv.2.1, none, cv.2.2.2),
      Function.update cs (Sum.inl 1) []⟩, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · show (TupTM MA MB).step ⟨some (Sum.inl Ctl.p2), cv, cs⟩ = _
      rw [step_p2 MA MB ⟨some (Sum.inl Ctl.p2), cv, cs⟩ rfl, p2_nil MA MB cv cs h1]
      rfl
    · simp
    · dsimp only
      rw [Function.update_of_ne hA]
      rfl
    · dsimp only
      rw [Function.update_of_ne hB]
      rfl
    · intro kt hk1 _ _
      dsimp only
      rw [Function.update_of_ne hk1]
  | cons b r ih =>
    intro C hl h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h1
    subst hl
    have hA1 : (Sum.inl 1 : TK MA MB) ≠ Sum.inr (Sum.inl MA.tm.k₀) := by simp
    have hB1 : (Sum.inl 1 : TK MA MB) ≠ Sum.inr (Sum.inr MB.tm.k₀) := by simp
    have hAB : (Sum.inr (Sum.inl MA.tm.k₀) : TK MA MB) ≠ Sum.inr (Sum.inr MB.tm.k₀) := by simp
    have hC1 : (TupTM MA MB).step ⟨some (Sum.inl Ctl.p2), cv, cs⟩ =
        some ⟨some (Sum.inl Ctl.p2), (cv.1, cv.2.1, some b, cv.2.2.2),
          Function.update (Function.update (Function.update cs (Sum.inl 1) r)
            (Sum.inr (Sum.inl MA.tm.k₀)) (MA.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inl MA.tm.k₀))))
            (Sum.inr (Sum.inr MB.tm.k₀)) (MB.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inr MB.tm.k₀)))⟩ := by
      rw [step_p2 MA MB ⟨some (Sum.inl Ctl.p2), cv, cs⟩ rfl, p2_cons MA MB cv cs b r h1]
      rfl
    have hI1 : Function.update (Function.update (Function.update cs (Sum.inl 1) r)
        (Sum.inr (Sum.inl MA.tm.k₀)) (MA.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inl MA.tm.k₀))))
        (Sum.inr (Sum.inr MB.tm.k₀)) (MB.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inr MB.tm.k₀)))
        (Sum.inl 1) = r := by
      rw [Function.update_of_ne hB1, Function.update_of_ne hA1, Function.update_self]
    obtain ⟨C', hC', hl', hv', hs1', hA', hB', hfr'⟩ := ih
      ⟨some (Sum.inl Ctl.p2), (cv.1, cv.2.1, some b, cv.2.2.2),
        Function.update (Function.update (Function.update cs (Sum.inl 1) r)
          (Sum.inr (Sum.inl MA.tm.k₀)) (MA.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inl MA.tm.k₀))))
          (Sum.inr (Sum.inr MB.tm.k₀)) (MB.inputAlphabet.invFun b :: cs (Sum.inr (Sum.inr MB.tm.k₀)))⟩
      rfl hI1
    refine ⟨C', ?_, hl', hv', hs1', ?_, ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply]
      change (flip bind (TupTM MA MB).step)^[r.length + 1]
        ((TupTM MA MB).step ⟨some (Sum.inl Ctl.p2), cv, cs⟩) = some C'
      rw [hC1]
      exact hC'
    · dsimp only at hA' ⊢
      rw [hA', Function.update_of_ne hAB, Function.update_self]
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    · dsimp only at hB' ⊢
      rw [hB', Function.update_self]
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    · intro kt hk1 hkA hkB
      dsimp only at hfr' ⊢
      rw [hfr' kt hk1 hkA hkB, Function.update_of_ne hkB, Function.update_of_ne hkA,
        Function.update_of_ne hk1]

/-- The copy phase: after `2 |x| + 2` steps the input is on the stacks of `MA` and of `MB`,
and the tupling machine is ready to run `MA`. -/
theorem copy_run (x : List Bool) :
    ∃ R : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[2 * x.length + 2] (some (initList (TupTM MA MB) x)) =
        some R ∧
      R.l = some (Sum.inr (Sum.inl MA.tm.main)) ∧
      R.var = (MA.tm.initialState, MB.tm.initialState, none, none) ∧
      (∀ k, R.stk (Sum.inr (Sum.inl k)) = (initList MA.tm (x.map MA.inputAlphabet.invFun)).stk k) ∧
      (∀ k, R.stk (Sum.inr (Sum.inr k)) = (initList MB.tm (x.map MB.inputAlphabet.invFun)).stk k) ∧
      R.stk (Sum.inl 0) = [] ∧ R.stk (Sum.inl 1) = [] ∧ R.stk (Sum.inl 2) = [] := by
  have hs0 : (initList (TupTM MA MB) x).stk (Sum.inl 0) = x := initList_stk_self' (TupTM MA MB) x
  have hs1 : (initList (TupTM MA MB) x).stk (Sum.inl 1) = [] :=
    initList_stk_ne' (TupTM MA MB) x (by simp)
  have hs2 : (initList (TupTM MA MB) x).stk (Sum.inl 2) = [] :=
    initList_stk_ne' (TupTM MA MB) x (by simp)
  obtain ⟨C1, hC1, hl1, hv1, hs01, hs11, hfr1⟩ :=
    pass1 MA MB x [] (initList (TupTM MA MB) x) rfl hs0 hs1
  obtain ⟨C2, hC2, hl2, hv2, hs12, hA2, hB2, hfr2⟩ :=
    pass2 MA MB x.reverse C1 hl1 (by rw [hs11, List.append_nil])
  refine ⟨C2, ?_, hl2, ?_, ?_, ?_, ?_, hs12, ?_⟩
  · have hlen : 2 * x.length + 2 = (x.reverse.length + 1) + (x.length + 1) := by
      simp; ring
    rw [hlen, Function.iterate_add_apply, hC1]
    exact hC2
  · rw [hv2, hv1]
    rfl
  · intro k
    by_cases hk : k = MA.tm.k₀
    · subst hk
      rw [hA2, hfr1 (Sum.inr (Sum.inl MA.tm.k₀)) (by simp) (by simp),
        initList_stk_ne' (TupTM MA MB) x (by simp), initList_stk_self' MA.tm _]
      simp
      rfl
    · rw [hfr2 (Sum.inr (Sum.inl k)) (by simp) (by simp [hk]) (by simp),
        hfr1 (Sum.inr (Sum.inl k)) (by simp) (by simp),
        initList_stk_ne' (TupTM MA MB) x (by simp), initList_stk_ne' MA.tm _ hk]
      rfl
  · intro k
    by_cases hk : k = MB.tm.k₀
    · subst hk
      rw [hB2, hfr1 (Sum.inr (Sum.inr MB.tm.k₀)) (by simp) (by simp),
        initList_stk_ne' (TupTM MA MB) x (by simp), initList_stk_self' MB.tm _]
      simp
      rfl
    · rw [hfr2 (Sum.inr (Sum.inr k)) (by simp) (by simp) (by simp [hk]),
        hfr1 (Sum.inr (Sum.inr k)) (by simp) (by simp),
        initList_stk_ne' (TupTM MA MB) x (by simp), initList_stk_ne' MB.tm _ hk]
      rfl
  · rw [hfr2 (Sum.inl 0) (by simp) (by simp) (by simp), hs01]
  · rw [hfr2 (Sum.inl 2) (by simp) (by simp) (by simp),
      hfr1 (Sum.inl 2) (by simp) (by simp), hs2]

theorem haltList_stk_self' (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

theorem haltList_stk_ne' (tm : FinTM2) (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := by
  simp [haltList, h]

theorem cfg_ext' {K : Type} {Γ : K → Type} {Λ σ : Type} (c d : TM2.Cfg Γ Λ σ)
    (h1 : c.l = d.l) (h2 : c.var = d.var) (h3 : c.stk = d.stk) : c = d := by
  obtain ⟨l1, v1, s1⟩ := c
  obtain ⟨l2, v2, s2⟩ := d
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem step_afterA (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.afterA)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.afterA) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

theorem step_afterB (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.afterB)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.afterB) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

theorem afterA_eval (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) :
    TM2.stepAux (ctlStmt MA MB Ctl.afterA) v S =
      { l := some (Sum.inr (Sum.inr MB.tm.main)),
        var := (v.1, v.2.1, v.2.2.1, (S (Sum.inr (Sum.inl MA.tm.k₁))).head?.map MA.outputAlphabet),
        stk := Function.update S (Sum.inr (Sum.inl MA.tm.k₁))
          (S (Sum.inr (Sum.inl MA.tm.k₁))).tail } := by
  rfl

/-- The tupling machine, run on `x`, halts with output `[a, b]` after `2 |x| + 2 + kA + 1 + kB + 1`
steps, provided `MA` (resp. `MB`) halts on `x` with output `a` (resp. `b`) in `kA` (resp. `kB`)
steps. -/
theorem tup_halts (x : List Bool) (a b : Bool) (kA kB : ℕ)
    (hA : (flip bind MA.tm.step)^[kA] (some (initList MA.tm (x.map MA.inputAlphabet.invFun))) =
      some (haltList MA.tm [MA.outputAlphabet.invFun a]))
    (hB : (flip bind MB.tm.step)^[kB] (some (initList MB.tm (x.map MB.inputAlphabet.invFun))) =
      some (haltList MB.tm [MB.outputAlphabet.invFun b])) :
    (flip bind (TupTM MA MB).step)^[2 * x.length + 2 + kA + 1 + kB + 1]
      (some (initList (TupTM MA MB) x)) = some (haltList (TupTM MA MB) [a, b]) := by
  obtain ⟨R, hC, hRl, hRv, hRA, hRB, hR0, hR1, hR2⟩ := copy_run MA MB x
  have relA0 : RelA MA MB (initList MA.tm (x.map MA.inputAlphabet.invFun)) R :=
    ⟨hRl, congrArg Prod.fst hRv, hRA⟩
  obtain ⟨RA, hRA_it, relA, frA⟩ :=
    runA MA MB kA (initList MA.tm (x.map MA.inputAlphabet.invFun))
      (haltList MA.tm [MA.outputAlphabet.invFun a]) R hA relA0
  have hRAl : RA.l = some (Sum.inl Ctl.afterA) := relA.1
  have hstA := step_afterA MA MB RA hRAl
  obtain ⟨RA1, hRA1def⟩ : ∃ RA1, RA1 = TM2.stepAux (ctlStmt MA MB Ctl.afterA) RA.var RA.stk :=
    ⟨_, rfl⟩
  have hstA' : (TupTM MA MB).step RA = some RA1 := by rw [hstA, hRA1def]
  -- the value written by `afterA`
  have hvB : RA.var.2.1 = MB.tm.initialState := by
    have h1 : RA.var.2.1 = R.var.2.1 := congrArg (fun s => s.1) frA.1
    have h2 : R.var.2.1 = MB.tm.initialState := congrArg (fun s => s.2.1) hRv
    exact h1.trans h2
  have relB0 : RelB MA MB (initList MB.tm (x.map MB.inputAlphabet.invFun)) RA1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hRA1def, afterA_eval]
      rfl
    · rw [hRA1def, afterA_eval]
      dsimp only
      exact hvB
    · intro k
      rw [hRA1def, afterA_eval]
      dsimp only
      have hne : (Sum.inr (Sum.inr k) : TK MA MB) ≠ Sum.inr (Sum.inl MA.tm.k₁) := by simp
      rw [Function.update_of_ne hne]
      exact (frA.2 _ (fun k' => by simp)).trans (hRB k)
  obtain ⟨RB, hRB_it, relB, frB⟩ :=
    runB MA MB kB (initList MB.tm (x.map MB.inputAlphabet.invFun))
      (haltList MB.tm [MB.outputAlphabet.invFun b]) RA1 hB relB0
  have hRBl : RB.l = some (Sum.inl Ctl.afterB) := relB.1
  -- facts about the configuration just before `afterB`
  have hBk1 : RB.stk (Sum.inr (Sum.inr MB.tm.k₁)) = [MB.outputAlphabet.invFun b] := by
    rw [relB.2.2 MB.tm.k₁]
    exact haltList_stk_self' MB.tm _
  have hBne : ∀ k, k ≠ MB.tm.k₁ → RB.stk (Sum.inr (Sum.inr k)) = [] := fun k hk => by
    rw [relB.2.2 k]
    exact haltList_stk_ne' MB.tm _ hk
  have hAll : ∀ k, RB.stk (Sum.inr (Sum.inl k)) = [] := by
    intro k
    rw [frB.2.2 (Sum.inr (Sum.inl k)) (fun k' => by simp), hRA1def, afterA_eval]
    dsimp only
    by_cases hk : k = MA.tm.k₁
    · subst hk
      rw [Function.update_self, relA.2.2 MA.tm.k₁, haltList_stk_self']
      rfl
    · rw [Function.update_of_ne (show (Sum.inr (Sum.inl k) : TK MA MB) ≠
          Sum.inr (Sum.inl MA.tm.k₁) by simp [hk]), relA.2.2 k, haltList_stk_ne' MA.tm _ hk]
      rfl
  have hLow0 : RB.stk (Sum.inl 0) = [] := by
    rw [frB.2.2 (Sum.inl 0) (fun k' => by simp), hRA1def, afterA_eval]
    dsimp only
    rw [Function.update_of_ne (show (Sum.inl 0 : TK MA MB) ≠ Sum.inr (Sum.inl MA.tm.k₁) by simp),
      frA.2 (Sum.inl 0) (fun k' => by simp), hR0]
  have hLow1 : RB.stk (Sum.inl 1) = [] := by
    rw [frB.2.2 (Sum.inl 1) (fun k' => by simp), hRA1def, afterA_eval]
    dsimp only
    rw [Function.update_of_ne (show (Sum.inl 1 : TK MA MB) ≠ Sum.inr (Sum.inl MA.tm.k₁) by simp),
      frA.2 (Sum.inl 1) (fun k' => by simp), hR1]
  have hLow2 : RB.stk (Sum.inl 2) = [] := by
    rw [frB.2.2 (Sum.inl 2) (fun k' => by simp), hRA1def, afterA_eval]
    dsimp only
    rw [Function.update_of_ne (show (Sum.inl 2 : TK MA MB) ≠ Sum.inr (Sum.inl MA.tm.k₁) by simp),
      frA.2 (Sum.inl 2) (fun k' => by simp), hR2]
  -- the two registers: `r2` holds the bit of `MA`, `r1` the bit of `MB` (written by `afterB`)
  have hr2 : RB.var.2.2.2 = some a := by
    rw [frB.2.1, hRA1def, afterA_eval]
    dsimp only
    rw [relA.2.2 MA.tm.k₁, haltList_stk_self']
    show some (MA.outputAlphabet (MA.outputAlphabet.invFun a)) = some a
    exact congrArg some (MA.outputAlphabet.apply_symm_apply a)
  -- the bit of `MB`, read from its output stack
  have hr1 : ((RB.stk (Sum.inr (Sum.inr MB.tm.k₁))).head?.map MB.outputAlphabet).getD false = b := by
    rw [hBk1]
    show (some (MB.outputAlphabet (MB.outputAlphabet.invFun b))).getD false = b
    rw [Option.getD_some]
    exact MB.outputAlphabet.apply_symm_apply b
  -- the final configuration
  have hfin_stk : (TM2.stepAux (ctlStmt MA MB Ctl.afterB) RB.var RB.stk).stk =
      (haltList (TupTM MA MB) [a, b]).stk := by
    funext kt
    simp only [ctlStmt, TM2.stepAux, haltList]
    by_cases h2 : kt = Sum.inl 2
    · subst h2
      simp [Function.update_apply, hLow2, hr2, hr1]
    · rcases kt with i | k | k
      · fin_cases i
        · simp [Function.update_apply, hLow0]
        · simp [Function.update_apply, hLow1]
        · exact absurd rfl h2
      · simp [Function.update_apply, hAll]
      · by_cases hk : k = MB.tm.k₁
        · subst hk
          simp [Function.update_apply, hBk1]
          rfl
        · have hne1 : (Sum.inr (Sum.inr k) : TK MA MB) ≠ Sum.inl 2 := by simp
          have hne2 : (Sum.inr (Sum.inr k) : TK MA MB) ≠ Sum.inr (Sum.inr MB.tm.k₁) := by
            simp [hk]
          simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
          rw [hBne k hk]
          simp [haltList, hk]
  have hfin : TM2.stepAux (ctlStmt MA MB Ctl.afterB) RB.var RB.stk =
      haltList (TupTM MA MB) [a, b] :=
    cfg_ext' _ _ rfl rfl hfin_stk
  -- compose the runs
  have h2 : (flip bind (TupTM MA MB).step)^[2 * x.length + 2 + kA]
      (some (initList (TupTM MA MB) x)) = some RA := by
    rw [show 2 * x.length + 2 + kA = kA + (2 * x.length + 2) by omega,
      Function.iterate_add_apply, hC]
    exact hRA_it
  have h3 : (flip bind (TupTM MA MB).step)^[2 * x.length + 2 + kA + 1]
      (some (initList (TupTM MA MB) x)) = some RA1 := by
    rw [Function.iterate_succ_apply', h2]
    exact hstA'
  have h4 : (flip bind (TupTM MA MB).step)^[2 * x.length + 2 + kA + 1 + kB]
      (some (initList (TupTM MA MB) x)) = some RB := by
    rw [show 2 * x.length + 2 + kA + 1 + kB = kB + (2 * x.length + 2 + kA + 1) by omega,
      Function.iterate_add_apply, h3]
    exact hRB_it
  rw [Function.iterate_succ_apply', h4]
  show (TupTM MA MB).step RB = _
  rw [step_afterB MA MB RB hRBl, hfin]
  rfl

end Defs

/-- Parallel composition: two polynomial-time machines on one input return both answers. -/
theorem main : ∀ L M : Lang, InP L → InP M →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun p : Bool × Bool => [p.1, p.2]) (fun x => (L x, M x))) := by
  intro L M hL hM
  obtain ⟨hA⟩ := hL
  obtain ⟨hB⟩ := hM
  refine ⟨{ tm := TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux,
            inputAlphabet := Equiv.refl Bool,
            outputAlphabet := Equiv.refl Bool,
            time := Polynomial.C 2 * Polynomial.X + Polynomial.C 4 + hA.time + hB.time,
            outputsFun := fun a => ?_ }⟩
  have hAa := hA.outputsFun a
  have hBa := hB.outputsFun a
  unfold TM2OutputsInTime at hAa hBa ⊢
  have hida : (List.map (Equiv.refl Bool).invFun (id a) :
      List ((TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux).Γ
        (TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux).k₀)) = a := List.map_id a
  refine ⟨⟨2 * a.length + 2 + hAa.steps + 1 + hBa.steps + 1, ?_⟩, ?_⟩
  · have key := tup_halts hA.toTM2ComputableAux hB.toTM2ComputableAux a (L a) (M a)
      hAa.steps hBa.steps hAa.evals_in_steps hBa.evals_in_steps
    have key2 : (flip bind (TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux).step)^[
        2 * a.length + 2 + hAa.steps + 1 + hBa.steps + 1]
        (some (initList (TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux)
          (List.map (Equiv.refl Bool).invFun (id a)))) =
        some (haltList (TupTM hA.toTM2ComputableAux hB.toTM2ComputableAux) [L a, M a]) := by
      rw [hida]
      exact key
    exact key2
  · have hA' : hAa.steps ≤ hA.time.eval a.length := hAa.steps_le_m
    have hB' : hBa.steps ≤ hB.time.eval a.length := hBa.steps_le_m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      List.length_map, id]
    omega

end MPP.Solutions.Pnp009
