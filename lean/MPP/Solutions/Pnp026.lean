import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp023

namespace MPP.Solutions.Pnp026

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
  | p1 | p2 | afterA | afterB | t1 | t2

def ctlDecEq : DecidableEq Ctl := fun x y => by
  cases x <;> cases y <;> first | exact isTrue rfl | exact isFalse (fun h => by cases h)

def ctlFintype : Fintype Ctl := by
  haveI := ctlDecEq
  exact Fintype.ofList [Ctl.p1, Ctl.p2, Ctl.afterA, Ctl.afterB, Ctl.t1, Ctl.t2] (by intro x; cases x <;> simp)

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
    -- move the output list of `MA` to the buffer `inl 1`, one bit per step (reversing it)
    .peek (Sum.inr (Sum.inl MA.tm.k₁)) (fun s x => (s.1, s.2.1, x.map MA.outputAlphabet, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.pop (Sum.inr (Sum.inl MA.tm.k₁)) (fun s _ => s)
          (.push (Sum.inl 1) (fun s => s.2.2.1.getD false) (.goto (fun _ => Sum.inl Ctl.afterA))))
        (.goto (fun _ => Sum.inr (Sum.inr MB.tm.main))))
  | .afterB =>
    -- move the output list of `MB` to the buffer `inl 0` (empty since the input was copied)
    .peek (Sum.inr (Sum.inr MB.tm.k₁)) (fun s x => (s.1, s.2.1, x.map MB.outputAlphabet, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.pop (Sum.inr (Sum.inr MB.tm.k₁)) (fun s _ => s)
          (.push (Sum.inl 0) (fun s => s.2.2.1.getD false) (.goto (fun _ => Sum.inl Ctl.afterB))))
        (.goto (fun _ => Sum.inl Ctl.t1)))
  | .t1 =>
    -- move the buffer `inl 0` (the output of `MB`, reversed) to the output stack `inl 2`
    .peek (Sum.inl 0) (fun s x => (s.1, s.2.1, x, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.pop (Sum.inl 0) (fun s _ => s)
          (.push (Sum.inl 2) (fun s => s.2.2.1.getD false) (.goto (fun _ => Sum.inl Ctl.t1))))
        (.push (Sum.inl 2) (fun _ => true)
          (.push (Sum.inl 2) (fun _ => false) (.goto (fun _ => Sum.inl Ctl.t2)))))
  | .t2 =>
    -- write the output of `MA` doubled in front of the separator, from the buffer `inl 1`
    .peek (Sum.inl 1) (fun s x => (s.1, s.2.1, x, s.2.2.2))
      (.branch (fun s => s.2.2.1.isSome)
        (.pop (Sum.inl 1) (fun s _ => s)
          (.push (Sum.inl 2) (fun s => s.2.2.1.getD false)
            (.push (Sum.inl 2) (fun s => s.2.2.1.getD false) (.goto (fun _ => Sum.inl Ctl.t2)))))
        (.load (fun _ => (MA.tm.initialState, MB.tm.initialState, none, none)) .halt))

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
      simp [h1] <;> rfl
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

theorem step_t1 (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.t1)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.t1) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

theorem step_t2 (C : (TupTM MA MB).Cfg) (hl : C.l = some (Sum.inl Ctl.t2)) :
    (TupTM MA MB).step C = some (TM2.stepAux (ctlStmt MA MB Ctl.t2) C.var C.stk) := by
  obtain ⟨cl, cv, cs⟩ := C
  simp only at hl
  subst hl
  rfl

/-- One machine step, as an iterate of the step function. -/
theorem iter_succ_of (n : ℕ) (C C1 : (TupTM MA MB).Cfg) (h : (TupTM MA MB).step C = some C1) :
    (flip bind (TupTM MA MB).step)^[n + 1] (some C) = (flip bind (TupTM MA MB).step)^[n] (some C1) := by
  rw [Function.iterate_succ_apply]
  congr 1

/-- Doubling of every bit, as the pair encoding does it. -/
def dbl (x : List Bool) : List Bool := x.flatMap fun b => [b, b]

theorem dbl_append (x y : List Bool) : dbl (x ++ y) = dbl x ++ dbl y := by
  simp [dbl, List.flatMap_append]

theorem dbl_cons (b : Bool) (x : List Bool) : dbl (b :: x) = b :: b :: dbl x := by
  simp [dbl, List.flatMap_cons]

/-! One control step of each loop, as an explicit configuration. -/

theorem eqA_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt))
    (h : S (Sum.inr (Sum.inl MA.tm.k₁)) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.afterA) v S =
      ⟨some (Sum.inr (Sum.inr MB.tm.main)), (v.1, v.2.1, none, v.2.2.2), S⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqA_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (a : MA.tm.Γ MA.tm.k₁)
    (l : List (MA.tm.Γ MA.tm.k₁)) (h : S (Sum.inr (Sum.inl MA.tm.k₁)) = a :: l) :
    TM2.stepAux (ctlStmt MA MB Ctl.afterA) v S =
      ⟨some (Sum.inl Ctl.afterA), (v.1, v.2.1, some (MA.outputAlphabet a), v.2.2.2),
        Function.update (Function.update S (Sum.inr (Sum.inl MA.tm.k₁)) l) (Sum.inl 1)
          (MA.outputAlphabet a :: S (Sum.inl 1))⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqB_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt))
    (h : S (Sum.inr (Sum.inr MB.tm.k₁)) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.afterB) v S =
      ⟨some (Sum.inl Ctl.t1), (v.1, v.2.1, none, v.2.2.2), S⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqB_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (b : MB.tm.Γ MB.tm.k₁)
    (l : List (MB.tm.Γ MB.tm.k₁)) (h : S (Sum.inr (Sum.inr MB.tm.k₁)) = b :: l) :
    TM2.stepAux (ctlStmt MA MB Ctl.afterB) v S =
      ⟨some (Sum.inl Ctl.afterB), (v.1, v.2.1, some (MB.outputAlphabet b), v.2.2.2),
        Function.update (Function.update S (Sum.inr (Sum.inr MB.tm.k₁)) l) (Sum.inl 0)
          (MB.outputAlphabet b :: S (Sum.inl 0))⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqT1_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (h : S (Sum.inl 0) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.t1) v S =
      ⟨some (Sum.inl Ctl.t2), (v.1, v.2.1, none, v.2.2.2),
        Function.update (Function.update S (Sum.inl 2) (true :: S (Sum.inl 2))) (Sum.inl 2)
          (false :: (Function.update S (Sum.inl 2) (true :: S (Sum.inl 2))) (Sum.inl 2))⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqT1_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (b : Bool) (l : List Bool)
    (h : S (Sum.inl 0) = b :: l) :
    TM2.stepAux (ctlStmt MA MB Ctl.t1) v S =
      ⟨some (Sum.inl Ctl.t1), (v.1, v.2.1, some b, v.2.2.2),
        Function.update (Function.update S (Sum.inl 0) l) (Sum.inl 2) (b :: S (Sum.inl 2))⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqT2_nil (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (h : S (Sum.inl 1) = []) :
    TM2.stepAux (ctlStmt MA MB Ctl.t2) v S =
      ⟨none, (MA.tm.initialState, MB.tm.initialState, none, none), S⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

theorem eqT2_cons (v : TS MA MB) (S : ∀ kt, List (TG MA MB kt)) (b : Bool) (l : List Bool)
    (h : S (Sum.inl 1) = b :: l) :
    TM2.stepAux (ctlStmt MA MB Ctl.t2) v S =
      ⟨some (Sum.inl Ctl.t2), (v.1, v.2.1, some b, v.2.2.2),
        Function.update (Function.update (Function.update S (Sum.inl 1) l) (Sum.inl 2)
          (b :: S (Sum.inl 2))) (Sum.inl 2)
          (b :: (Function.update (Function.update S (Sum.inl 1) l) (Sum.inl 2)
            (b :: S (Sum.inl 2))) (Sum.inl 2))⟩ := by
  simp only [ctlStmt, TM2.stepAux]
  rw [h]
  rfl

/-- The output loop of `MA`: move its output list to the buffer `inl 1`, reversing it. -/
theorem loopA (L : List (MA.tm.Γ MA.tm.k₁)) : ∀ (C : (TupTM MA MB).Cfg) (B : List Bool),
    C.l = some (Sum.inl Ctl.afterA) → C.stk (Sum.inr (Sum.inl MA.tm.k₁)) = L →
    C.stk (Sum.inl 1) = B →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[L.length + 1] (some C) = some C' ∧
      C'.l = some (Sum.inr (Sum.inr MB.tm.main)) ∧
      C'.var = (C.var.1, C.var.2.1, none, C.var.2.2.2) ∧
      C'.stk (Sum.inr (Sum.inl MA.tm.k₁)) = [] ∧
      C'.stk (Sum.inl 1) = (L.map MA.outputAlphabet).reverse ++ B ∧
      ∀ kt, kt ≠ Sum.inr (Sum.inl MA.tm.k₁) → kt ≠ Sum.inl 1 → C'.stk kt = C.stk kt := by
  induction L with
  | nil =>
    intro C B hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.afterA), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs) := step_afterA MA MB _ rfl
    refine ⟨TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one]
      exact hs
    · rw [eqA_nil MA MB cv cs h0]
    · rw [eqA_nil MA MB cv cs h0]
    · rw [eqA_nil MA MB cv cs h0]
      exact h0
    · rw [eqA_nil MA MB cv cs h0]
      simp [h1] <;> rfl
    · intro kt _ _
      rw [eqA_nil MA MB cv cs h0]
  | cons a L ih =>
    intro C B hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.afterA), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs) := step_afterA MA MB _ rfl
    have hC1 := eqA_cons MA MB cv cs a L h0
    have hl1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs).l = some (Sum.inl Ctl.afterA) := by
      rw [hC1]
    have hv1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs).var =
        (cv.1, cv.2.1, some (MA.outputAlphabet a), cv.2.2.2) := by
      rw [hC1]
    have hs0 : (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs).stk
        (Sum.inr (Sum.inl MA.tm.k₁)) = L := by
      rw [hC1]
      simp [Function.update_apply]
    have hs1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs).stk (Sum.inl 1) =
        MA.outputAlphabet a :: B := by
      rw [hC1]
      simp [h1] <;> rfl
    have hfr : ∀ kt, kt ≠ Sum.inr (Sum.inl MA.tm.k₁) → kt ≠ Sum.inl 1 →
        (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs).stk kt = cs kt := by
      intro kt hk1 hk2
      rw [hC1]
      simp [Function.update_apply, hk1, hk2]
    obtain ⟨C', hC', hl', hv', hs0', hs1', hfr'⟩ :=
      ih (TM2.stepAux (ctlStmt MA MB Ctl.afterA) cv cs) (MA.outputAlphabet a :: B) hl1 hs0 hs1
    refine ⟨C', ?_, hl', ?_, hs0', ?_, ?_⟩
    · rw [List.length_cons, iter_succ_of MA MB _ _ _ hs]
      exact hC'
    · rw [hv', hv1]
    · rw [hs1']
      simp [List.reverse_cons, List.append_assoc]
    · intro kt hk1 hk2
      rw [hfr' kt hk1 hk2, hfr kt hk1 hk2]

/-- The output loop of `MB`: move its output list to the buffer `inl 0`, reversing it. -/
theorem loopB (L : List (MB.tm.Γ MB.tm.k₁)) : ∀ (C : (TupTM MA MB).Cfg) (B : List Bool),
    C.l = some (Sum.inl Ctl.afterB) → C.stk (Sum.inr (Sum.inr MB.tm.k₁)) = L →
    C.stk (Sum.inl 0) = B →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[L.length + 1] (some C) = some C' ∧
      C'.l = some (Sum.inl Ctl.t1) ∧
      C'.var = (C.var.1, C.var.2.1, none, C.var.2.2.2) ∧
      C'.stk (Sum.inr (Sum.inr MB.tm.k₁)) = [] ∧
      C'.stk (Sum.inl 0) = (L.map MB.outputAlphabet).reverse ++ B ∧
      ∀ kt, kt ≠ Sum.inr (Sum.inr MB.tm.k₁) → kt ≠ Sum.inl 0 → C'.stk kt = C.stk kt := by
  induction L with
  | nil =>
    intro C B hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.afterB), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs) := step_afterB MA MB _ rfl
    refine ⟨TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one]
      exact hs
    · rw [eqB_nil MA MB cv cs h0]
    · rw [eqB_nil MA MB cv cs h0]
    · rw [eqB_nil MA MB cv cs h0]
      exact h0
    · rw [eqB_nil MA MB cv cs h0]
      simp [h1] <;> rfl
    · intro kt _ _
      rw [eqB_nil MA MB cv cs h0]
  | cons b L ih =>
    intro C B hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.afterB), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs) := step_afterB MA MB _ rfl
    have hC1 := eqB_cons MA MB cv cs b L h0
    have hl1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs).l = some (Sum.inl Ctl.afterB) := by
      rw [hC1]
    have hv1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs).var =
        (cv.1, cv.2.1, some (MB.outputAlphabet b), cv.2.2.2) := by
      rw [hC1]
    have hs0 : (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs).stk
        (Sum.inr (Sum.inr MB.tm.k₁)) = L := by
      rw [hC1]
      simp [Function.update_apply]
    have hs1 : (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs).stk (Sum.inl 0) =
        MB.outputAlphabet b :: B := by
      rw [hC1]
      simp [h1] <;> rfl
    have hfr : ∀ kt, kt ≠ Sum.inr (Sum.inr MB.tm.k₁) → kt ≠ Sum.inl 0 →
        (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs).stk kt = cs kt := by
      intro kt hk1 hk2
      rw [hC1]
      simp [Function.update_apply, hk1, hk2]
    obtain ⟨C', hC', hl', hv', hs0', hs1', hfr'⟩ :=
      ih (TM2.stepAux (ctlStmt MA MB Ctl.afterB) cv cs) (MB.outputAlphabet b :: B) hl1 hs0 hs1
    refine ⟨C', ?_, hl', ?_, hs0', ?_, ?_⟩
    · rw [List.length_cons, iter_succ_of MA MB _ _ _ hs]
      exact hC'
    · rw [hv', hv1]
    · rw [hs1']
      simp [List.reverse_cons, List.append_assoc]
    · intro kt hk1 hk2
      rw [hfr' kt hk1 hk2, hfr kt hk1 hk2]

/-- The transfer of `MB`'s output from `inl 0` to the output stack, then the separator. -/
theorem loopT1 (Lb : List Bool) : ∀ (C : (TupTM MA MB).Cfg) (O : List Bool),
    C.l = some (Sum.inl Ctl.t1) → C.stk (Sum.inl 0) = Lb → C.stk (Sum.inl 2) = O →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[Lb.length + 1] (some C) = some C' ∧
      C'.l = some (Sum.inl Ctl.t2) ∧
      C'.var = (C.var.1, C.var.2.1, none, C.var.2.2.2) ∧
      C'.stk (Sum.inl 0) = [] ∧
      C'.stk (Sum.inl 2) = false :: true :: (Lb.reverse ++ O) ∧
      ∀ kt, kt ≠ Sum.inl 0 → kt ≠ Sum.inl 2 → C'.stk kt = C.stk kt := by
  induction Lb with
  | nil =>
    intro C O hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.t1), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs) := step_t1 MA MB _ rfl
    refine ⟨TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one]
      exact hs
    · rw [eqT1_nil MA MB cv cs h0]
    · rw [eqT1_nil MA MB cv cs h0]
    · rw [eqT1_nil MA MB cv cs h0]
      simp [Function.update_apply, h0] <;> rfl
    · rw [eqT1_nil MA MB cv cs h0]
      simp [Function.update_apply, h1] <;> rfl
    · intro kt hk0 hk2
      rw [eqT1_nil MA MB cv cs h0]
      simp [Function.update_apply, hk0, hk2]
  | cons b Lb ih =>
    intro C O hl h0 h1
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h0 h1
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.t1), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs) := step_t1 MA MB _ rfl
    have hC1 := eqT1_cons MA MB cv cs b Lb h0
    have hl1 : (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs).l = some (Sum.inl Ctl.t1) := by
      rw [hC1]
    have hv1 : (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs).var =
        (cv.1, cv.2.1, some b, cv.2.2.2) := by
      rw [hC1]
    have hs0 : (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs).stk (Sum.inl 0) = Lb := by
      rw [hC1]
      simp [Function.update_apply]
    have hs2 : (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs).stk (Sum.inl 2) = b :: O := by
      rw [hC1]
      simp [Function.update_apply, h1] <;> rfl
    have hfr : ∀ kt, kt ≠ Sum.inl 0 → kt ≠ Sum.inl 2 →
        (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs).stk kt = cs kt := by
      intro kt hk0 hk2
      rw [hC1]
      simp [Function.update_apply, hk0, hk2]
    obtain ⟨C', hC', hl', hv', hs0', hs2', hfr'⟩ :=
      ih (TM2.stepAux (ctlStmt MA MB Ctl.t1) cv cs) (b :: O) hl1 hs0 hs2
    refine ⟨C', ?_, hl', ?_, hs0', ?_, ?_⟩
    · rw [List.length_cons, iter_succ_of MA MB _ _ _ hs]
      exact hC'
    · rw [hv', hv1]
    · rw [hs2']
      simp [List.reverse_cons, List.append_assoc]
    · intro kt hk0 hk2
      rw [hfr' kt hk0 hk2, hfr kt hk0 hk2]

/-- The transfer of `MA`'s output from `inl 1` to the output stack, doubling every bit. -/
theorem loopT2 (Lb : List Bool) : ∀ (C : (TupTM MA MB).Cfg) (O : List Bool),
    C.l = some (Sum.inl Ctl.t2) → C.stk (Sum.inl 1) = Lb → C.stk (Sum.inl 2) = O →
    ∃ C' : (TupTM MA MB).Cfg,
      (flip bind (TupTM MA MB).step)^[Lb.length + 1] (some C) = some C' ∧
      C'.l = none ∧
      C'.var = (MA.tm.initialState, MB.tm.initialState, none, none) ∧
      C'.stk (Sum.inl 1) = [] ∧
      C'.stk (Sum.inl 2) = dbl Lb.reverse ++ O ∧
      ∀ kt, kt ≠ Sum.inl 1 → kt ≠ Sum.inl 2 → C'.stk kt = C.stk kt := by
  induction Lb with
  | nil =>
    intro C O hl h1 h2
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h1 h2
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.t2), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs) := step_t2 MA MB _ rfl
    refine ⟨TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_nil, zero_add, Function.iterate_one]
      exact hs
    · rw [eqT2_nil MA MB cv cs h1]
    · rw [eqT2_nil MA MB cv cs h1]
    · rw [eqT2_nil MA MB cv cs h1]
      exact h1
    · rw [eqT2_nil MA MB cv cs h1]
      simp [dbl, h2] <;> rfl
    · intro kt _ _
      rw [eqT2_nil MA MB cv cs h1]
  | cons b Lb ih =>
    intro C O hl h1 h2
    obtain ⟨cl, cv, cs⟩ := C
    simp only at hl h1 h2
    subst hl
    have hs : (TupTM MA MB).step ⟨some (Sum.inl Ctl.t2), cv, cs⟩ =
        some (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs) := step_t2 MA MB _ rfl
    have hC1 := eqT2_cons MA MB cv cs b Lb h1
    have hl1 : (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs).l = some (Sum.inl Ctl.t2) := by
      rw [hC1]
    have hs1 : (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs).stk (Sum.inl 1) = Lb := by
      rw [hC1]
      simp [Function.update_apply]
    have hs2 : (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs).stk (Sum.inl 2) = b :: b :: O := by
      rw [hC1]
      simp [Function.update_apply, h2] <;> rfl
    have hfr : ∀ kt, kt ≠ Sum.inl 1 → kt ≠ Sum.inl 2 →
        (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs).stk kt = cs kt := by
      intro kt hk1 hk2
      rw [hC1]
      simp [Function.update_apply, hk1, hk2]
    obtain ⟨C', hC', hl', hv', hs1', hs2', hfr'⟩ :=
      ih (TM2.stepAux (ctlStmt MA MB Ctl.t2) cv cs) (b :: b :: O) hl1 hs1 hs2
    refine ⟨C', ?_, hl', hv', hs1', ?_, ?_⟩
    · rw [List.length_cons, iter_succ_of MA MB _ _ _ hs]
      exact hC'
    · rw [hs2', List.reverse_cons, dbl_append]
      simp [dbl, List.append_assoc]
    · intro kt hk1 hk2
      rw [hfr' kt hk1 hk2, hfr kt hk1 hk2]

/-- Mapping a list of bits to a letter type and back is the identity. -/
theorem map_inv_out {α : Type} (e : α ≃ Bool) (l : List Bool) :
    (l.map e.invFun).map e = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons, List.map_cons, ih]
    congr 1
    exact e.apply_symm_apply b

/-- Composition of two runs on the tupling machine. -/
theorem iter_comp (m E : ℕ) (C C' : (TupTM MA MB).Cfg) (x0 : (TupTM MA MB).Cfg)
    (h : (flip bind (TupTM MA MB).step)^[E] (some x0) = some C)
    (h2 : (flip bind (TupTM MA MB).step)^[m] (some C) = some C') :
    (flip bind (TupTM MA MB).step)^[m + E] (some x0) = some C' := by
  rw [Function.iterate_add_apply, h]
  exact h2

/-- Packing of the two runs: the tupling machine halts with `pair ya yb`. -/
theorem tup_list (x : List Bool) (ya yb : List Bool) (kA kB : ℕ)
    (hA : (flip bind MA.tm.step)^[kA] (some (initList MA.tm (x.map MA.inputAlphabet.invFun))) =
      some (haltList MA.tm (ya.map MA.outputAlphabet.invFun)))
    (hB : (flip bind MB.tm.step)^[kB] (some (initList MB.tm (x.map MB.inputAlphabet.invFun))) =
      some (haltList MB.tm (yb.map MB.outputAlphabet.invFun))) :
    (flip bind (TupTM MA MB).step)^[(ya.length + 1) + ((yb.length + 1) + ((yb.length + 1) +
        (kB + ((ya.length + 1) + (kA + (2 * x.length + 2))))))]
      (some (initList (TupTM MA MB) x)) =
      some (haltList (TupTM MA MB) (MPP.PvsNP.pair ya yb)) := by
  obtain ⟨R, hC, hRl, hRv, hRA, hRB, hR0, hR1, hR2⟩ := copy_run MA MB x
  have relA0 : RelA MA MB (initList MA.tm (x.map MA.inputAlphabet.invFun)) R :=
    ⟨hRl, congrArg Prod.fst hRv, hRA⟩
  obtain ⟨RA, hRA_it, relA, frA⟩ :=
    runA MA MB kA (initList MA.tm (x.map MA.inputAlphabet.invFun))
      (haltList MA.tm (ya.map MA.outputAlphabet.invFun)) R hA relA0
  have hRAl : RA.l = some (Sum.inl Ctl.afterA) := relA.1
  have hRAk1 : RA.stk (Sum.inr (Sum.inl MA.tm.k₁)) = ya.map MA.outputAlphabet.invFun := by
    rw [relA.2.2 MA.tm.k₁]
    exact haltList_stk_self' MA.tm _
  have hRA1 : RA.stk (Sum.inl 1) = [] := by
    rw [frA.2 (Sum.inl 1) (fun k' => by simp), hR1]
  obtain ⟨CA, hCA_it, hCAl, hCAv, hCAk, hCA1, hCAfr⟩ :=
    loopA MA MB (ya.map MA.outputAlphabet.invFun) RA [] hRAl hRAk1 hRA1
  rw [List.length_map] at hCA_it
  have hCA1' : CA.stk (Sum.inl 1) = ya.reverse := by
    rw [hCA1, map_inv_out MA.outputAlphabet ya, List.append_nil]
  have h21 : RA.var.2.1 = MB.tm.initialState := by
    have h := congrArg (fun s => s.1) frA.1
    simp only at h
    rw [h, hRv]
  have relB0 : RelB MA MB (initList MB.tm (x.map MB.inputAlphabet.invFun)) CA := by
    refine ⟨hCAl, ?_, ?_⟩
    · rw [hCAv]
      exact h21
    · intro k
      rw [hCAfr (Sum.inr (Sum.inr k)) (by simp) (by simp),
        frA.2 (Sum.inr (Sum.inr k)) (fun k' => by simp), hRB k]
  obtain ⟨RB, hRB_it, relB, frB⟩ :=
    runB MA MB kB (initList MB.tm (x.map MB.inputAlphabet.invFun))
      (haltList MB.tm (yb.map MB.outputAlphabet.invFun)) CA hB relB0
  have hRBl : RB.l = some (Sum.inl Ctl.afterB) := relB.1
  have hRBk : RB.stk (Sum.inr (Sum.inr MB.tm.k₁)) = yb.map MB.outputAlphabet.invFun := by
    rw [relB.2.2 MB.tm.k₁]
    exact haltList_stk_self' MB.tm _
  have hRB0 : RB.stk (Sum.inl 0) = [] := by
    rw [frB.2.2 (Sum.inl 0) (fun k' => by simp), hCAfr (Sum.inl 0) (by simp) (by simp),
      frA.2 (Sum.inl 0) (fun k' => by simp), hR0]
  have hRB1 : RB.stk (Sum.inl 1) = ya.reverse := by
    rw [frB.2.2 (Sum.inl 1) (fun k' => by simp), hCA1']
  have hRB2 : RB.stk (Sum.inl 2) = [] := by
    rw [frB.2.2 (Sum.inl 2) (fun k' => by simp), hCAfr (Sum.inl 2) (by simp) (by simp),
      frA.2 (Sum.inl 2) (fun k' => by simp), hR2]
  have hRBinr : ∀ k, RB.stk (Sum.inr (Sum.inl k)) = [] := by
    intro k
    rw [frB.2.2 (Sum.inr (Sum.inl k)) (fun k' => by simp)]
    by_cases hk : k = MA.tm.k₁
    · subst hk
      exact hCAk
    · rw [hCAfr (Sum.inr (Sum.inl k)) (by simp [hk]) (by simp), relA.2.2 k]
      exact haltList_stk_ne' MA.tm _ hk
  obtain ⟨CB, hCB_it, hCBl, hCBv, hCBk, hCB0, hCBfr⟩ :=
    loopB MA MB (yb.map MB.outputAlphabet.invFun) RB [] hRBl hRBk hRB0
  rw [List.length_map] at hCB_it
  have hCB0' : CB.stk (Sum.inl 0) = yb.reverse := by
    rw [hCB0, map_inv_out MB.outputAlphabet yb, List.append_nil]
  have hCB1 : CB.stk (Sum.inl 1) = ya.reverse := by
    rw [hCBfr (Sum.inl 1) (by simp) (by simp), hRB1]
  have hCB2 : CB.stk (Sum.inl 2) = [] := by
    rw [hCBfr (Sum.inl 2) (by simp) (by simp), hRB2]
  obtain ⟨CT1, hCT1_it, hCT1l, hCT1v, hCT10, hCT12, hCT1fr⟩ :=
    loopT1 MA MB yb.reverse CB [] hCBl hCB0' hCB2
  rw [List.length_reverse] at hCT1_it
  have hCT12' : CT1.stk (Sum.inl 2) = false :: true :: yb := by
    rw [hCT12, List.reverse_reverse, List.append_nil]
  have hCT11 : CT1.stk (Sum.inl 1) = ya.reverse := by
    rw [hCT1fr (Sum.inl 1) (by simp) (by simp), hCB1]
  obtain ⟨CT2, hCT2_it, hCT2l, hCT2v, hCT21, hCT22, hCT2fr⟩ :=
    loopT2 MA MB ya.reverse CT1 (false :: true :: yb) hCT1l hCT11 hCT12'
  rw [List.length_reverse] at hCT2_it
  -- the chain of runs
  have hE1 := iter_comp MA MB kA _ R RA _ hC hRA_it
  have hE2 := iter_comp MA MB (ya.length + 1) _ RA CA _ hE1 hCA_it
  have hE3 := iter_comp MA MB kB _ CA RB _ hE2 hRB_it
  have hE4 := iter_comp MA MB (yb.length + 1) _ RB CB _ hE3 hCB_it
  have hE5 := iter_comp MA MB (yb.length + 1) _ CB CT1 _ hE4 hCT1_it
  have hE6 := iter_comp MA MB (ya.length + 1) _ CT1 CT2 _ hE5 hCT2_it
  rw [hE6]
  congr 1
  have key0 : CT2.stk (Sum.inl 0) = [] := by
    rw [hCT2fr (Sum.inl 0) (by simp) (by simp), hCT10]
  have key1 : CT2.stk (Sum.inl 1) = [] := hCT21
  have key2 : CT2.stk (Sum.inl 2) = dbl ya.reverse.reverse ++ (false :: true :: yb) := hCT22
  refine cfg_ext' _ _ ?_ ?_ ?_
  · rw [hCT2l]
    rfl
  · rw [hCT2v]
    rfl
  · funext kt
    rcases kt with i | k | k
    · fin_cases i
      · show CT2.stk (Sum.inl 0) = (haltList (TupTM MA MB) (MPP.PvsNP.pair ya yb)).stk (Sum.inl 0)
        rw [key0]
        exact (haltList_stk_ne' (TupTM MA MB) _ (show Sum.inl 0 ≠ Sum.inl 2 by simp)).symm
      · show CT2.stk (Sum.inl 1) = (haltList (TupTM MA MB) (MPP.PvsNP.pair ya yb)).stk (Sum.inl 1)
        rw [key1]
        exact (haltList_stk_ne' (TupTM MA MB) _ (show Sum.inl 1 ≠ Sum.inl 2 by simp)).symm
      · show CT2.stk (Sum.inl 2) = (haltList (TupTM MA MB) (MPP.PvsNP.pair ya yb)).stk (Sum.inl 2)
        rw [key2, show (haltList (TupTM MA MB) (MPP.PvsNP.pair ya yb)).stk (Sum.inl 2) =
          MPP.PvsNP.pair ya yb from haltList_stk_self' (TupTM MA MB) _]
        simp [MPP.PvsNP.pair, dbl, List.append_assoc]
    · rw [hCT2fr (Sum.inr (Sum.inl k)) (by simp) (by simp), hCT1fr (Sum.inr (Sum.inl k)) (by simp) (by simp),
        hCBfr (Sum.inr (Sum.inl k)) (by simp) (by simp), hRBinr k]
      exact (haltList_stk_ne' (TupTM MA MB) _ (show Sum.inr (Sum.inl k) ≠ Sum.inl 2 by simp)).symm
    · by_cases hk : k = MB.tm.k₁
      · subst hk
        rw [hCT2fr (Sum.inr (Sum.inr _)) (by simp) (by simp), hCT1fr (Sum.inr (Sum.inr _)) (by simp) (by simp),
          hCBk]
        exact (haltList_stk_ne' (TupTM MA MB) _ (show Sum.inr (Sum.inr MB.tm.k₁) ≠ Sum.inl 2 by simp)).symm
      · rw [hCT2fr (Sum.inr (Sum.inr k)) (by simp) (by simp), hCT1fr (Sum.inr (Sum.inr k)) (by simp) (by simp),
          hCBfr (Sum.inr (Sum.inr k)) (by simp [hk]) (by simp), relB.2.2 k, haltList_stk_ne' MB.tm _ hk]
        exact (haltList_stk_ne' (TupTM MA MB) _ (show Sum.inr (Sum.inr k) ≠ Sum.inl 2 by simp)).symm

end Defs

/-- Pair encoding of two polynomial-time maps: one machine runs both on the same input. -/
theorem main : ∀ f g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) →
    ∃ h : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) h) ∧
      ∀ z : List Bool, h z = pair (f z) (g z) := by
  intro f g hf hg
  obtain ⟨T⟩ := hf
  obtain ⟨U⟩ := hg
  obtain ⟨qf, hqf⟩ := MPP.Solutions.Pnp023.main f ⟨T⟩
  obtain ⟨qg, hqg⟩ := MPP.Solutions.Pnp023.main g ⟨U⟩
  refine ⟨fun z => pair (f z) (g z),
    ⟨{ tm := TupTM T.toTM2ComputableAux U.toTM2ComputableAux,
       inputAlphabet := Equiv.refl Bool,
       outputAlphabet := Equiv.refl Bool,
       time := Polynomial.C 2 * Polynomial.X + Polynomial.C 6 + T.time + U.time +
         Polynomial.C 2 * qf + Polynomial.C 2 * qg,
       outputsFun := fun x => ?_ }⟩, fun z => rfl⟩
  have hAa := T.outputsFun x
  have hBa := U.outputsFun x
  unfold TM2OutputsInTime at hAa hBa ⊢
  have hidx : (List.map (Equiv.refl Bool).invFun (id x) :
      List ((TupTM T.toTM2ComputableAux U.toTM2ComputableAux).Γ
        (TupTM T.toTM2ComputableAux U.toTM2ComputableAux).k₀)) = x := List.map_id x
  have hidp : (List.map (Equiv.refl Bool).invFun (id (pair (f x) (g x))) :
      List ((TupTM T.toTM2ComputableAux U.toTM2ComputableAux).Γ
        (TupTM T.toTM2ComputableAux U.toTM2ComputableAux).k₁)) = pair (f x) (g x) :=
    List.map_id _
  have hA' : hAa.steps ≤ T.time.eval x.length := hAa.steps_le_m
  have hB' : hBa.steps ≤ U.time.eval x.length := hBa.steps_le_m
  have hqf' := hqf x
  have hqg' := hqg x
  refine ⟨⟨(f x).length + 1 + ((g x).length + 1 + ((g x).length + 1 + (hBa.steps +
    ((f x).length + 1 + (hAa.steps + (2 * x.length + 2)))))), ?_⟩, ?_⟩
  · rw [hidx, hidp]
    exact tup_list T.toTM2ComputableAux U.toTM2ComputableAux x (f x) (g x) hAa.steps hBa.steps
      hAa.evals_in_steps hBa.evals_in_steps
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      List.length_map, id_eq]
    omega


end MPP.Solutions.Pnp026
