import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp006

namespace MPP.Solutions.Pnp066

open Turing MPP.Solutions.Pnp006

/-- A dummy machine whose only role is to supply Bool-valued physical stacks. -/
def drv : FinTM2 where
  K := Bool
  k₀ := true
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := TM2.Stmt.halt

section Machine

variable (B : FinTM2) [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

/-- Labels of the loop machine: those of the body, and nine control labels. -/
abbrev Lc := B.Λ ⊕ Fin 9

/-- States: the body's state, a register holding a popped symbol, and a flag. -/
abbrev Sc := B.σ × Option Bool × Bool

/-- The initial state of the loop machine. -/
def initSc : Sc B := (B.initialState, none, false)

/-- The body's stacks sit on the physical stacks `inr k`. -/
def embB : Emb drv B (Lc B) (Sc B) B where
  ι := Sum.inr
  ε := fun _ => Equiv.refl _
  lab := Sum.inl
  π := fun s => s.1
  set := fun v s => (v, s.2.1, s.2.2)
  haltTo := Sum.inr 5
  ι_inj := Sum.inr_injective
  set_π := fun _ => rfl
  π_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl

/-- Control label `i`. -/
def lbl (i : Fin 9) : Lc B := Sum.inr i

variable {B}

/-- The physical stacks: `D` is the data (the body's input and the output), `E` is the body's
output stack, `F` and `C` are Bool stacks for the move and the counter. -/
def D : drv.K ⊕ B.K := Sum.inr B.k₀
def E : drv.K ⊕ B.K := Sum.inr B.k₁
def F : drv.K ⊕ B.K := Sum.inl true
def C : drv.K ⊕ B.K := Sum.inl false

/-- Bits as a list on the Bool stack `F` (the identity, made explicit for the types). -/
def bitsF (l : List Bool) : List (Phys drv B F) := l

/-- Bits as a list on the Bool stack `C`. -/
def bitsC (l : List Bool) : List (Phys drv B C) := l

variable (B) (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool)

/-- The nine control statements. The labels are: 0 decode, 1 compare, 2 move data to counter,
3 move back, 4 counter test, 5 move body output, 6 clear data, 7 enter body, 8 finish. -/
noncomputable def ctlStmt : Fin 9 → TM2.Stmt (Phys drv B) (Lc B) (Sc B)
  | 0 => TM2.Stmt.pop D (fun s x => (s.1, x.map eIn, s.2.2))
      (TM2.Stmt.branch (fun s => s.2.1.isSome) (TM2.Stmt.goto (fun _ => lbl B 1))
        (TM2.Stmt.goto (fun _ => lbl B 2)))
  | 1 => TM2.Stmt.pop D (fun s y => (s.1, s.2.1, decide (s.2.1 = y.map eIn)))
      (TM2.Stmt.branch (fun s => s.2.2)
        (TM2.Stmt.push F (fun s => s.2.1.getD false) (TM2.Stmt.goto (fun _ => lbl B 0)))
        (TM2.Stmt.goto (fun _ => lbl B 2)))
  | 2 => TM2.Stmt.pop D (fun s x => (s.1, x.map eIn, s.2.2))
      (TM2.Stmt.branch (fun s => s.2.1.isSome)
        (TM2.Stmt.push C (fun s => s.2.1.getD false) (TM2.Stmt.goto (fun _ => lbl B 2)))
        (TM2.Stmt.goto (fun _ => lbl B 3)))
  | 3 => TM2.Stmt.pop F (fun s x => (s.1, x, s.2.2))
      (TM2.Stmt.branch (fun s => s.2.1.isSome)
        (TM2.Stmt.push D (fun s => eIn.symm (s.2.1.getD false)) (TM2.Stmt.goto (fun _ => lbl B 3)))
        (TM2.Stmt.goto (fun _ => lbl B 4)))
  | 4 => TM2.Stmt.pop C (fun s x => (s.1, x, x.isNone))
      (TM2.Stmt.goto (fun s => if s.2.2 then lbl B 8 else lbl B 7))
  | 5 => TM2.Stmt.pop E (fun s x => (s.1, x.map eOut, s.2.2))
      (TM2.Stmt.branch (fun s => s.2.1.isSome)
        (TM2.Stmt.push F (fun s => s.2.1.getD false) (TM2.Stmt.goto (fun _ => lbl B 5)))
        (TM2.Stmt.goto (fun _ => lbl B 6)))
  | 6 => TM2.Stmt.pop D (fun s x => (s.1, x.map (fun _ => true), s.2.2))
      (TM2.Stmt.branch (fun s => s.2.1.isSome)
        (TM2.Stmt.goto (fun _ => lbl B 6)) (TM2.Stmt.goto (fun _ => lbl B 3)))
  | 7 => TM2.Stmt.load (fun s => (B.initialState, s.2.1, s.2.2))
      (TM2.Stmt.goto (fun _ => Sum.inl B.main))
  | 8 => TM2.Stmt.load (fun _ => initSc B) TM2.Stmt.halt

variable {B}

/-- The statements of the loop machine. -/
noncomputable def Mc (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) :
    Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)
  | Sum.inl l => trS (embB B) (B.m l)
  | Sum.inr i => ctlStmt B eIn eOut i

end Machine

/-- The loop machine: it runs the body `B` on the data as many times as the counter says. -/
noncomputable def loopTM (B : FinTM2) [Fintype B.K] [Fintype B.Λ] [Fintype B.σ]
    [Fintype (B.Γ B.k₀)] (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) : FinTM2 where
  K := Bool ⊕ B.K
  k₀ := Sum.inr B.k₀
  k₁ := Sum.inr B.k₀
  Γ := Phys drv B
  Λ := Lc B
  main := lbl B 0
  σ := Sc B
  initialState := initSc B
  m := Mc eIn eOut
  Γk₀Fin := (inferInstance : Fintype (B.Γ B.k₀))

section Run

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

/-- `c` runs to `c'` in exactly `k` steps of the machine `M`. -/
def Run (M : Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)) (k : ℕ)
    (c c' : TM2.Cfg (Phys drv B) (Lc B) (Sc B)) : Prop :=
  (flip bind (TM2.step M))^[k] (some c) = some c'

theorem run_one (M : Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)) {c c' : TM2.Cfg (Phys drv B) (Lc B) (Sc B)}
    (h : TM2.step M c = some c') : Run M 1 c c' := by
  unfold Run
  rw [Function.iterate_one]
  exact h

theorem run_trans (M : Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)) {k₁ k₂ : ℕ}
    {c c' c'' : TM2.Cfg (Phys drv B) (Lc B) (Sc B)} (h₁ : Run M k₁ c c') (h₂ : Run M k₂ c' c'') :
    Run M (k₂ + k₁) c c'' := by
  unfold Run at *
  rw [Function.iterate_add_apply, h₁]
  exact h₂

/-- A loop that moves the content of stack `src` onto stack `dst`, with the conversions `cv` and
`dv`. The label `lp` is the loop, and it exits to `nxt`. -/
theorem mv_run (M : Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)) (src dst : drv.K ⊕ B.K)
    (hne : src ≠ dst) (cv : Phys drv B src → Bool) (dv : Bool → Phys drv B dst)
    (f : Sc B → Option (Phys drv B src) → Sc B) (g : Sc B → Phys drv B dst) (lp nxt : Lc B)
    (hM : M lp = TM2.Stmt.pop src f (TM2.Stmt.branch (fun s => s.2.1.isSome)
      (TM2.Stmt.push dst g (TM2.Stmt.goto (fun _ => lp))) (TM2.Stmt.goto (fun _ => nxt))))
    (hf : ∀ s x, f s x = (s.1, x.map cv, s.2.2))
    (hg : ∀ s b, s.2.1 = some b → g s = dv b) :
    ∀ (L : List (Phys drv B src)) (s : Sc B) (S : ∀ p, List (Phys drv B p)), S src = L →
      Run M (L.length + 1) ⟨some lp, s, S⟩
        ⟨some nxt, (s.1, none, s.2.2),
          Function.update (Function.update S src []) dst ((L.map (dv ∘ cv)).reverse ++ S dst)⟩ := by
  intro L
  induction L with
  | nil =>
    intro s S hS
    apply run_one
    simp only [TM2.step, TM2.stepAux, hM, hf, hS, List.map_nil, List.reverse_nil, List.nil_append,
      List.head?_nil, Option.map_none, Option.isSome_none, cond_false]
    have hu : Function.update S src [] = S := by
      rw [Function.update_eq_self_iff]
      exact hS.symm
    simp only [List.tail_nil, hu, Function.update_eq_self, List.map_nil, List.reverse_nil,
      List.nil_append]
  | cons a L ih =>
    intro s S hS
    have hstep : TM2.step M ⟨some lp, s, S⟩ = some ⟨some lp, (s.1, some (cv a), s.2.2),
        Function.update (Function.update S src L) dst (dv (cv a) :: (Function.update S src L) dst)⟩ := by
      simp only [TM2.step, TM2.stepAux, hM, hf, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, cond_true]
      rw [hg (s.1, some (cv a), s.2.2) (cv a) rfl]
    have hS1 : Function.update (Function.update S src L) dst
        (dv (cv a) :: (Function.update S src L) dst) src = L := by
      rw [Function.update_of_ne hne, Function.update_self]
    have key := ih (s.1, some (cv a), s.2.2) _ hS1
    have hrun := run_trans M (run_one M hstep) key
    have e : (a :: L).length + 1 = L.length + 1 + 1 := by simp
    have hstk : Function.update (Function.update (Function.update (Function.update S src L) dst
        (dv (cv a) :: Function.update S src L dst)) src [])
        dst ((List.map (dv ∘ cv) L).reverse ++
          Function.update (Function.update S src L) dst (dv (cv a) :: Function.update S src L dst) dst)
        = Function.update (Function.update S src []) dst ((List.map (dv ∘ cv) (a :: L)).reverse ++ S dst) := by
      funext p
      by_cases hp : p = dst
      · subst hp
        simp [Function.update_apply, hne, hne.symm, List.reverse_cons, List.append_assoc]
      · by_cases hs : p = src
        · subst hs
          simp [Function.update_apply, hp, hne, hne.symm]
        · simp [Function.update_apply, hp, hs]
    rw [e, ← hstk]
    simpa using hrun

/-- A loop that only empties stack `src`. -/
theorem clr_run (M : Lc B → TM2.Stmt (Phys drv B) (Lc B) (Sc B)) (src : drv.K ⊕ B.K)
    (f : Sc B → Option (Phys drv B src) → Sc B) (lp nxt : Lc B)
    (hM : M lp = TM2.Stmt.pop src f (TM2.Stmt.branch (fun s => s.2.1.isSome)
      (TM2.Stmt.goto (fun _ => lp)) (TM2.Stmt.goto (fun _ => nxt))))
    (hf : ∀ s x, f s x = (s.1, x.map (fun _ => true), s.2.2)) :
    ∀ (L : List (Phys drv B src)) (s : Sc B) (S : ∀ p, List (Phys drv B p)), S src = L →
      Run M (L.length + 1) ⟨some lp, s, S⟩
        ⟨some nxt, (s.1, none, s.2.2), Function.update S src []⟩ := by
  intro L
  induction L with
  | nil =>
    intro s S hS
    apply run_one
    have hu : Function.update S src [] = S := by
      rw [Function.update_eq_self_iff]
      exact hS.symm
    simp only [TM2.step, TM2.stepAux, hM, hf, hS, List.head?_nil, Option.map_none,
      Option.isSome_none, cond_false, List.tail_nil, hu, Option.map_none]
  | cons a L ih =>
    intro s S hS
    have hstep : TM2.step M ⟨some lp, s, S⟩ = some ⟨some lp, (s.1, some true, s.2.2),
        Function.update S src L⟩ := by
      simp only [TM2.step, TM2.stepAux, hM, hf, hS, List.head?_cons, List.tail_cons, Option.map_some,
        Option.isSome_some, cond_true]
    have key := ih (s.1, some true, s.2.2) (Function.update S src L)
      (by rw [Function.update_self])
    have hrun := run_trans M (run_one M hstep) key
    have e : (a :: L).length + 1 = L.length + 1 + 1 := by simp
    rw [e]
    have hstk : Function.update (Function.update S src L) src [] = Function.update S src [] := by
      rw [Function.update_idem]
    simpa [hstk] using hrun

end Run

section Sim

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

/-- A run of `k` steps of the body is a run of `k` steps of the loop machine, through the
embedding `embB`. -/
theorem body_sim (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (s0 : Sc B) :
    ∀ (k : ℕ) (c0 c : TM2.Cfg B.Γ B.Λ B.σ) (P0 : ∀ p, List (Phys drv B p)),
      (flip bind (TM2.step B.m))^[k] (some c0) = some c → Inv (embB B) c0.stk P0 →
      ∃ P, (flip bind (TM2.step (Mc eIn eOut)))^[k]
            (some ⟨liftL (embB B) c0.l, (embB B).set c0.var s0, P0⟩) =
          some ⟨liftL (embB B) c.l, (embB B).set c.var s0, P⟩ ∧
        Inv (embB B) c.stk P ∧ ∀ p, (∀ k', p ≠ (embB B).ι k') → P p = P0 p := by
  intro k
  induction k with
  | zero =>
    intro c0 c P0 h hI
    simp only [Function.iterate_zero_apply, id] at h
    cases h
    exact ⟨P0, rfl, hI, fun _ _ => rfl⟩
  | succ k ih =>
    intro c0 c P0 h hI
    rw [Function.iterate_succ_apply'] at h
    cases hk : (flip bind (TM2.step B.m))^[k] (some c0) with
    | none =>
      rw [hk] at h
      simp [flip] at h
    | some ck =>
      rw [hk] at h
      have h' : TM2.step B.m ck = some c := by simpa [flip] using h
      obtain ⟨P1, hit, hI1, hfr1⟩ := ih c0 ck P0 hk hI
      rcases ck with ⟨_ | l, v, S⟩
      · simp [TM2.step] at h'
      · have hc : TM2.stepAux (B.m l) v S = c := by simpa [TM2.step] using h'
        subst hc
        obtain ⟨P', hr, hI', hfr'⟩ :=
          stepAux_trS (embB B) (B.m l) v S (((embB B).set v s0)) P1 ((embB B).π_set _ _) hI1
        refine ⟨P', ?_, hI', fun p hp => (hfr' p hp).trans (hfr1 p hp)⟩
        rw [Function.iterate_succ_apply', hit]
        show TM2.step (Mc eIn eOut) ⟨some ((embB B).lab l), (embB B).set v s0, P1⟩ = _
        show some (TM2.stepAux (trS (embB B) (B.m l)) ((embB B).set v s0) P1) = _
        rw [hr, (embB B).set_set]

end Sim

section Decode

/-- The decoder of the pair encoding: matched doubled bits are collected, and the rest after
the first mismatched pair is the counter. -/
def decM : List Bool → List Bool × List Bool
  | [] => ([], [])
  | [_] => ([], [])
  | x :: y :: t => if x = y then (x :: (decM t).1, (decM t).2) else ([], t)

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

/-- Decoding a single symbol: two steps, the symbol is dropped. -/
theorem dec_single_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (xb : Bool)
    (s : Sc B) (S : ∀ p, List (Phys drv B p)) (hS : S D = [eIn.symm xb]) :
    Run (Mc eIn eOut) 2 ⟨some (lbl B 0), s, S⟩
      ⟨some (lbl B 2), (s.1, some xb, false), Function.update S D []⟩ := by
  have h1 : TM2.step (Mc eIn eOut) ⟨some (lbl B 0), s, S⟩ =
      some ⟨some (lbl B 1), (s.1, some xb, s.2.2), Function.update S D []⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, hS, List.head?, List.tail,
      Option.map, Option.isSome, cond, Equiv.apply_symm_apply]
    rfl
  have h2 : TM2.step (Mc eIn eOut) ⟨some (lbl B 1), (s.1, some xb, s.2.2), Function.update S D []⟩ =
      some ⟨some (lbl B 2), (s.1, some xb, false), Function.update S D []⟩ := by
    simp [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl]
  exact run_trans _ (run_one _ h1) (run_one _ h2)

/-- Decoding a mismatched pair: two steps, both symbols are dropped and the decoder exits. -/
theorem dec_mis_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (xb yb : Bool) (t : List Bool)
    (s : Sc B) (S : ∀ p, List (Phys drv B p)) (hxy : xb ≠ yb)
    (hS : S D = (xb :: yb :: t).map eIn.symm) :
    Run (Mc eIn eOut) 2 ⟨some (lbl B 0), s, S⟩
      ⟨some (lbl B 2), (s.1, some xb, false), Function.update S D (t.map eIn.symm)⟩ := by
  have h1 : TM2.step (Mc eIn eOut) ⟨some (lbl B 0), s, S⟩ =
      some ⟨some (lbl B 1), (s.1, some xb, s.2.2),
        Function.update S D ((yb :: t).map eIn.symm)⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, hS, List.map, List.head?, List.tail,
      Option.map, Option.isSome, cond, Equiv.apply_symm_apply]
    rfl
  have h2 : TM2.step (Mc eIn eOut)
      ⟨some (lbl B 1), (s.1, some xb, s.2.2), Function.update S D ((yb :: t).map eIn.symm)⟩ =
      some ⟨some (lbl B 2), (s.1, some xb, false), Function.update S D (t.map eIn.symm)⟩ := by
    have hd : decide (some xb = some yb) = false := by simp [hxy]
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, List.map, List.head?, List.tail,
      Option.map, Option.isSome, cond, Equiv.apply_symm_apply, Function.update_self,
      Function.update_idem, hd]
  exact run_trans _ (run_one _ h1) (run_one _ h2)

/-- Decoding a matched pair: two steps, both symbols are dropped and the bit is pushed on `F`. -/
theorem dec_match_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (xb : Bool) (t : List Bool)
    (s : Sc B) (S : ∀ p, List (Phys drv B p)) (hS : S D = (xb :: xb :: t).map eIn.symm) :
    Run (Mc eIn eOut) 2 ⟨some (lbl B 0), s, S⟩
      ⟨some (lbl B 0), (s.1, some xb, true),
        Function.update (Function.update S D (t.map eIn.symm)) F (xb :: S F)⟩ := by
  have h1 : TM2.step (Mc eIn eOut) ⟨some (lbl B 0), s, S⟩ =
      some ⟨some (lbl B 1), (s.1, some xb, s.2.2),
        Function.update S D ((xb :: t).map eIn.symm)⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, hS, List.map, List.head?, List.tail,
      Option.map, Option.isSome, cond, Equiv.apply_symm_apply]
    rfl
  have hFD : F ≠ (D : drv.K ⊕ B.K) := by intro h; unfold F D at h; cases h
  have h2 : TM2.step (Mc eIn eOut)
      ⟨some (lbl B 1), (s.1, some xb, s.2.2), Function.update S D ((xb :: t).map eIn.symm)⟩ =
      some ⟨some (lbl B 0), (s.1, some xb, true),
        Function.update (Function.update S D (t.map eIn.symm)) F (xb :: S F)⟩ := by
    have hd : decide (some xb = some xb) = true := by simp
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, List.map, List.head?, List.tail,
      Option.map, Option.isSome, cond, Equiv.apply_symm_apply, Function.update_self,
      Function.update_idem, hd, Option.getD, Function.update_of_ne hFD]
    rfl
  exact run_trans _ (run_one _ h1) (run_one _ h2)

theorem dec_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) : ∀ (n : ℕ) (a : List Bool),
    a.length ≤ n → ∀ (s : Sc B) (S : ∀ p, List (Phys drv B p)), S D = a.map eIn.symm →
    ∃ k, k ≤ a.length + 2 ∧ ∃ (s' : Sc B) (S' : ∀ p, List (Phys drv B p)),
      Run (Mc eIn eOut) k ⟨some (lbl B 0), s, S⟩ ⟨some (lbl B 2), s', S'⟩ ∧
      S' D = (decM a).2.map eIn.symm ∧ S' F = bitsF ((decM a).1.reverse) ++ S F ∧
      ∀ p, p ≠ D → p ≠ F → S' p = S p := by
  intro n
  induction n with
  | zero =>
    intro a ha s S hS
    have ha' : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ha'
    have hS' : S D = [] := by rw [hS]; rfl
    have hFD : F ≠ (D : drv.K ⊕ B.K) := by intro h; unfold F D at h; cases h
    refine ⟨1, by simp, (s.1, none, s.2.2), Function.update S D [], run_one _ ?_, ?_, ?_, ?_⟩
    · simp [TM2.step, TM2.stepAux, Mc, ctlStmt, hS', lbl]
      rfl
    · simp [decM]
      rfl
    · simp [decM, bitsF, Function.update_of_ne hFD]
      rfl
    · intro p hp _
      simp [Function.update_of_ne hp]
  | succ n ih =>
    intro a ha s S hS
    have hFD : F ≠ (D : drv.K ⊕ B.K) := by intro h; unfold F D at h; cases h
    rcases a with _ | ⟨x, _ | ⟨y, t⟩⟩
    · have hS' : S D = [] := by rw [hS]; rfl
      refine ⟨1, by simp, (s.1, none, s.2.2), Function.update S D [], run_one _ ?_, ?_, ?_, ?_⟩
      · simp [TM2.step, TM2.stepAux, Mc, ctlStmt, hS', lbl]
        rfl
      · simp [decM]
        rfl
      · simp [decM, bitsF, Function.update_of_ne hFD]
        rfl
      · intro p hp _
        simp [Function.update_of_ne hp]
    · refine ⟨2, by simp, (s.1, some x, false), Function.update S D [],
        dec_single_run eIn eOut x s S hS, ?_, ?_, ?_⟩
      · simp [decM]
        rfl
      · simp [decM, bitsF, Function.update_of_ne hFD]
        rfl
      · intro p hp _
        simp [Function.update_of_ne hp]
    · by_cases hxy : x = y
      · subst hxy
        have hlen : t.length ≤ n := by simp at ha; omega
        have hS2 : Function.update (Function.update S D (t.map eIn.symm)) F (x :: S F) D
            = t.map eIn.symm := by
          rw [Function.update_of_ne hFD.symm, Function.update_self]
          rfl
        obtain ⟨k, hk, s', S', hrun, hD', hF', hfr'⟩ :=
          ih t hlen (s.1, some x, true) _ hS2
        refine ⟨k + 2, by simp at ha ⊢; omega, s', S',
          run_trans _ (dec_match_run eIn eOut x t s S hS) hrun, ?_, ?_, ?_⟩
        · rw [show decM (x :: x :: t) = (x :: (decM t).1, (decM t).2) by simp [decM]]
          exact hD'
        · have hbf : ∀ l1 l2 : List Bool, bitsF (B := B) (l1 ++ l2) =
              bitsF (B := B) l1 ++ bitsF (B := B) l2 := fun _ _ => rfl
          rw [show decM (x :: x :: t) = (x :: (decM t).1, (decM t).2) by simp [decM], hF',
            Function.update_self, List.reverse_cons, hbf, List.append_assoc]
          rfl
        · intro p hp1 hp2
          rw [hfr' p hp1 hp2]
          simp [Function.update_of_ne hp1, Function.update_of_ne hp2]
      · refine ⟨2, by simp, (s.1, some x, false), Function.update S D (t.map eIn.symm),
          dec_mis_run eIn eOut x y t s S hxy hS, ?_, ?_, ?_⟩
        · simp [decM, hxy]
          rfl
        · simp [decM, hxy, bitsF, Function.update_of_ne hFD]
          rfl
        · intro p hp _
          simp [Function.update_of_ne hp]

end Decode

section Round

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

theorem map_embB_symm (k : B.K) (l : List (B.Γ k)) : List.map (⇑((embB B).ε k).symm) l = l := by
  simp only [embB]
  exact List.map_id _

theorem bitsF_map_rev (f : Bool → B.Γ B.k₀) (l : List Bool) :
    (List.map (fun x => f x) (bitsF (B := B) l.reverse)).reverse = l.map f := by
  show (List.map f l.reverse).reverse = l.map f
  rw [← List.map_reverse, List.reverse_reverse]

/-- One round: pop one counter symbol, run the body on the data, move its output back to the
data stack, and return to the counter test. -/
theorem round_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (g : List Bool → List Bool)
    (hlen : ∀ z, (g z).length = z.length + 1) (T0 : ℕ) (w : List Bool) (b : Bool) (c : List Bool)
    (s : Sc B) (S : ∀ p, List (Phys drv B p))
    (hB : ∃ tb, tb ≤ T0 ∧ (flip bind (TM2.step B.m))^[tb] (some (initList B (w.map eIn.symm))) =
      some (haltList B ((g w).map eOut.symm)))
    (hD : S D = w.map eIn.symm) (hC : S C = bitsC (b :: c))
    (hO : ∀ p, p ≠ D → p ≠ C → S p = []) :
    ∃ t, t ≤ T0 + 2 * w.length + 8 ∧ ∃ (s' : Sc B) (S' : ∀ p, List (Phys drv B p)),
      Run (Mc eIn eOut) t ⟨some (lbl B 4), s, S⟩ ⟨some (lbl B 4), s', S'⟩ ∧
      S' D = (g w).map eIn.symm ∧ S' C = bitsC c ∧ ∀ p, p ≠ D → p ≠ C → S' p = [] := by
  obtain ⟨tb, htb, hbr⟩ := hB
  have hFD : F ≠ (D : drv.K ⊕ B.K) := by intro h; unfold F D at h; cases h
  have hCD : C ≠ (D : drv.K ⊕ B.K) := by intro h; unfold C D at h; cases h
  have hCF : C ≠ (F : drv.K ⊕ B.K) := by intro h; unfold C F at h; cases h
  have hCE : C ≠ (E : drv.K ⊕ B.K) := by intro h; unfold C E at h; cases h
  have hEF : (E : drv.K ⊕ B.K) ≠ F := by intro h; unfold E F at h; cases h
  -- the counter test pops one symbol and enters the body
  have hA1 : TM2.step (Mc eIn eOut) ⟨some (lbl B 4), s, S⟩ =
      some ⟨some (lbl B 7), (s.1, some b, false), Function.update S C (bitsC c)⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, hC, bitsC, List.head?, List.tail,
      Option.isNone, cond]
    rfl
  have hA2 : TM2.step (Mc eIn eOut)
      ⟨some (lbl B 7), (s.1, some b, false), Function.update S C (bitsC c)⟩ =
      some ⟨some (Sum.inl B.main), (B.initialState, some b, false),
        Function.update S C (bitsC c)⟩ := by
    simp [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl]
  -- the body starts from an empty configuration on the other stacks
  have hInv : Inv (embB B) (initList B (w.map eIn.symm)).stk
      (Function.update S C (bitsC c)) := by
    intro k
    have hkC : (Sum.inr k : drv.K ⊕ B.K) ≠ C := fun h => Sum.inr_ne_inl h
    by_cases hk : k = B.k₀
    · subst hk
      rw [initList_stk_self', map_embB_symm]
      show Function.update S C (bitsC c) (Sum.inr B.k₀) = _
      rw [Function.update_of_ne hkC]
      exact hD
    · rw [initList_stk_ne' B _ hk, map_embB_symm]
      show Function.update S C (bitsC c) (Sum.inr k) = _
      rw [Function.update_of_ne hkC]
      have hkD : (Sum.inr k : drv.K ⊕ B.K) ≠ D := fun h => hk (Sum.inr_injective h)
      exact hO _ hkD hkC
  obtain ⟨P, hP, hIP, hfrP⟩ := body_sim eIn eOut (B.initialState, some b, false) tb _ _ _ hbr hInv
  have hR1 : Run (Mc eIn eOut) tb ⟨some (Sum.inl B.main), (B.initialState, some b, false),
      Function.update S C (bitsC c)⟩ ⟨some (Sum.inr 5), (B.initialState, some b, false), P⟩ := hP
  have hPE : P E = (g w).map eOut.symm := by
    have h := hIP B.k₁
    rw [haltList_stk_self'] at h
    exact h.trans (map_embB_symm _ _)
  have hPF : P F = [] := by
    rw [hfrP F (fun k' h => Sum.inl_ne_inr h), Function.update_of_ne hCF.symm]
    exact hO F hFD hCF.symm
  have hPC : P C = bitsC c := by
    rw [hfrP C (fun k' h => Sum.inl_ne_inr h), Function.update_self]
  -- the body's output moves from `E` to `F`
  have hmEF := mv_run (Mc eIn eOut) E F hEF eOut (fun x => x)
    (fun s x => (s.1, x.map eOut, s.2.2)) (fun s => s.2.1.getD false) (lbl B 5) (lbl B 6) rfl
    (fun _ _ => rfl) (fun s x h => by simp [h]) (P E) (B.initialState, some b, false) P rfl
  -- the data stack is empty after the move
  have hD1 : ∀ X : List (Phys drv B F), (Function.update (Function.update P E []) F X) D = [] := by
    intro X
    by_cases hkk : B.k₀ = B.k₁
    · have hDE : (D : drv.K ⊕ B.K) = E := by unfold D E; rw [hkk]
      rw [Function.update_of_ne hFD.symm, hDE, Function.update_self]
    · have hDE : (D : drv.K ⊕ B.K) ≠ E := fun h => hkk (Sum.inr_injective h)
      have hPD : P D = [] := by
        have h := hIP B.k₀
        rw [haltList_stk_ne' B _ hkk] at h
        simpa [embB, D] using h
      rw [Function.update_of_ne hFD.symm, Function.update_of_ne hDE, hPD]
  have hclr := clr_run (Mc eIn eOut) D (fun s x => (s.1, x.map (fun _ => true), s.2.2))
    (lbl B 6) (lbl B 3) rfl (fun _ _ => rfl) [] (B.initialState, none, false)
    (Function.update (Function.update P E []) F
      (((P E).map ((show Bool → Phys drv B F from fun x => x) ∘ eOut)).reverse ++ P F)) (hD1 _)
  -- the output, now on `F`, moves back to the data stack
  have hF2 : (Function.update (Function.update (Function.update P E []) F
      (((P E).map ((show Bool → Phys drv B F from fun x => x) ∘ eOut)).reverse ++ P F)) D [])
      F = bitsF ((g w).reverse) := by
    rw [Function.update_of_ne hFD, Function.update_self, hPE, hPF, List.append_nil]
    have hmm : ((g w).map eOut.symm).map ((show Bool → Phys drv B F from fun x => x) ∘ eOut) =
        bitsF (g w) := by
      rw [List.map_map]
      unfold bitsF
      simp [Function.comp_def]
      exact List.map_id _
    rw [hmm]
    rfl
  have hmFD := mv_run (Mc eIn eOut) F D hFD (fun x => x) (fun x => eIn.symm x)
    (fun s x => (s.1, x, s.2.2)) (fun s => eIn.symm (s.2.1.getD false)) (lbl B 3) (lbl B 4) rfl
    (fun s x => by cases x <;> rfl) (fun s b' h => by simp [h]) (bitsF ((g w).reverse))
    (B.initialState, none, false) _ hF2
  have hlenPE : (P E).length = w.length + 1 := by
    calc (P E).length = ((g w).map eOut.symm).length := by rw [hPE]; rfl
      _ = (g w).length := List.length_map _
      _ = w.length + 1 := hlen w
  have hlenB : (bitsF (B := B) ((g w).reverse)).length = w.length + 1 := by
    show (g w).reverse.length = w.length + 1
    rw [List.length_reverse, hlen]
  have R := run_trans _ (run_trans _ (run_trans _ (run_trans _ (run_trans _ (run_one _ hA1)
    (run_one _ hA2)) hR1) hmEF) hclr) hmFD
  refine ⟨_, ?_, _, _, R, ?_, ?_, ?_⟩
  · simp only [List.length_nil]
    omega
  · simp only [Function.update_self, List.append_nil]
    exact bitsF_map_rev eIn.symm (g w)
  · simp only [Function.update_of_ne hCD, Function.update_of_ne hCF, Function.update_of_ne hCE, hPC]
  · intro p hpD hpC
    rw [Function.update_of_ne hpD]
    by_cases hpF : p = F
    · subst hpF
      rw [Function.update_self]
    · rw [Function.update_of_ne hpF, Function.update_of_ne hpD, Function.update_of_ne hpF]
      by_cases hpE : p = E
      · subst hpE
        rw [Function.update_self]
      · rw [Function.update_of_ne hpE]
        rcases p with x | k
        · cases x
          · exact absurd rfl hpC
          · exact absurd rfl hpF
        · have h := hIP k
          rw [haltList_stk_ne' B _ (fun h' => hpE (by unfold E; rw [h']))] at h
          simpa [embB] using h

end Round

section Rounds

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

theorem dC_ne_D : (C : drv.K ⊕ B.K) ≠ D := by intro h; unfold C D at h; cases h

/-- With the counter empty, the machine finishes in two steps. -/
theorem final_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (s : Sc B)
    (S : ∀ p, List (Phys drv B p)) (hC : S C = []) :
    Run (Mc eIn eOut) 2 ⟨some (lbl B 4), s, S⟩ ⟨none, initSc B, Function.update S C []⟩ := by
  have h1 : TM2.step (Mc eIn eOut) ⟨some (lbl B 4), s, S⟩ =
      some ⟨some (lbl B 8), (s.1, none, true), Function.update S C []⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, hC, List.head?, List.tail, Option.isNone]
    rfl
  have h2 : TM2.step (Mc eIn eOut) ⟨some (lbl B 8), (s.1, none, true), Function.update S C []⟩ =
      some ⟨none, initSc B, Function.update S C []⟩ := by
    simp only [TM2.step, TM2.stepAux, Mc, ctlStmt, lbl, initSc]
  exact run_trans _ (run_one _ h1) (run_one _ h2)

/-- Rounds: with `m` counter symbols, the machine applies the body `m` times to the data. -/
theorem rounds_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (g : List Bool → List Bool)
    (hlen : ∀ z, (g z).length = z.length + 1) (q : Polynomial ℕ)
    (hbody : ∀ w : List Bool, ∃ tb, tb ≤ q.eval w.length ∧
      (flip bind (TM2.step B.m))^[tb] (some (initList B (w.map eIn.symm))) =
        some (haltList B ((g w).map eOut.symm))) :
    ∀ (m : ℕ) (w : List Bool) (s : Sc B) (S : ∀ p, List (Phys drv B p)) (c : List Bool),
      c.length = m → S D = w.map eIn.symm → S C = bitsC c →
      (∀ p, p ≠ D → p ≠ C → S p = []) →
      ∃ t, t ≤ m * (q.eval (w.length + m) + 2 * (w.length + m) + 8) + 2 ∧
        ∃ S' : (∀ p, List (Phys drv B p)),
          Run (Mc eIn eOut) t ⟨some (lbl B 4), s, S⟩ ⟨none, initSc B, S'⟩ ∧
          S' D = ((g^[m]) w).map eIn.symm ∧ ∀ p, p ≠ D → S' p = [] := by
  intro m
  induction m with
  | zero =>
    intro w s S c hc hD hC hO
    have hc' : c = [] := List.eq_nil_of_length_eq_zero hc
    subst hc'
    have hC' : S C = [] := by rw [hC]; rfl
    refine ⟨2, by simp, Function.update S C [], final_run eIn eOut s S hC', ?_, ?_⟩
    · rw [Function.iterate_zero_apply, Function.update_of_ne dC_ne_D.symm, hD]
    · intro p hp
      by_cases hpC : p = C
      · subst hpC
        rw [Function.update_self]
      · rw [Function.update_of_ne hpC]
        exact hO p hp hpC
  | succ m ih =>
    intro w s S c hc hD hC hO
    obtain ⟨b, c', rfl⟩ : ∃ b c', c = b :: c' := by
      cases c with
      | nil => simp at hc
      | cons b c' => exact ⟨b, c', rfl⟩
    have hc' : c'.length = m := by simpa using hc
    obtain ⟨tb, htb, hbr⟩ := hbody w
    obtain ⟨t1, ht1, s1, S1, hR1, hD1, hC1, hO1⟩ :=
      round_run eIn eOut g hlen (q.eval w.length) w b c' s S ⟨tb, htb, hbr⟩ hD hC hO
    obtain ⟨t2, ht2, S', hR2, hD2, hO2⟩ := ih (g w) s1 S1 c' hc' hD1 hC1 hO1
    refine ⟨t2 + t1, ?_, S', run_trans _ hR1 hR2, ?_, hO2⟩
    · rw [hlen] at ht2
      have e : w.length + 1 + m = w.length + (m + 1) := by omega
      rw [e] at ht2
      have hmono : q.eval w.length ≤ q.eval (w.length + (m + 1)) :=
        poly_mono q _ _ (by omega)
      have hsucc : (m + 1) * (q.eval (w.length + (m + 1)) + 2 * (w.length + (m + 1)) + 8) =
          m * (q.eval (w.length + (m + 1)) + 2 * (w.length + (m + 1)) + 8) +
            (q.eval (w.length + (m + 1)) + 2 * (w.length + (m + 1)) + 8) := Nat.succ_mul _ _
      nlinarith
    · rw [Function.iterate_succ_apply, hD2]

end Rounds

section Lengths

theorem decM_len : ∀ (n : ℕ) (a : List Bool), a.length ≤ n →
    (decM a).1.length + (decM a).2.length ≤ a.length := by
  intro n
  induction n with
  | zero =>
    intro a ha
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [decM]
  | succ n ih =>
    intro a ha
    rcases a with _ | ⟨x, _ | ⟨y, t⟩⟩
    · simp [decM]
    · simp [decM]
    · by_cases hxy : x = y
      · subst hxy
        have := ih t (by simp at ha; omega)
        simp only [decM, if_true, List.length_cons]
        simp at this ⊢
        omega
      · simp [decM, hxy]
        omega

theorem decM_pair (z u : List Bool) : decM (MPP.PvsNP.pair z u) = (z, u) := by
  induction z with
  | nil => simp [MPP.PvsNP.pair, decM]
  | cons b z ih =>
    have e : MPP.PvsNP.pair (b :: z) u = b :: b :: MPP.PvsNP.pair z u := by
      simp [MPP.PvsNP.pair]
    rw [e]
    simp [decM, ih]

end Lengths

section Main

variable {B : FinTM2} [Fintype B.K] [Fintype B.Λ] [Fintype B.σ] [Fintype (B.Γ B.k₀)]

theorem dC_ne_F : (C : drv.K ⊕ B.K) ≠ F := by intro h; unfold C F at h; cases h

theorem map_idC (l : List Bool) :
    List.map (fun x : Bool => (x : Phys drv B C)) l = bitsC (B := B) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, ih]
    rfl

/-- The input stacks: the data on `D`, all other stacks empty. -/
def initStk (eIn : B.Γ B.k₀ ≃ Bool) (a : List Bool) : ∀ p, List (Phys drv B p) :=
  Function.update (fun p => ([] : List (Phys drv B p))) D (a.map eIn.symm)

theorem initStk_ne (eIn : B.Γ B.k₀ ≃ Bool) (a : List Bool) {p : drv.K ⊕ B.K} (hp : p ≠ D) :
    initStk eIn a p = [] := by
  unfold initStk
  rw [Function.update_of_ne hp]

/-- Decoding, then moving the counter onto `C` and the data back onto `D`. -/
theorem pre_rounds (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (g : List Bool → List Bool)
    (hlen : ∀ z, (g z).length = z.length + 1) (a : List Bool) :
    ∃ t0, t0 ≤ a.length + 4 + (decM a).2.length + (decM a).1.length ∧
      ∃ (s3 : Sc B) (S3 : ∀ p, List (Phys drv B p)),
        Run (Mc eIn eOut) t0 ⟨some (lbl B 0), initSc B, initStk eIn a⟩
          ⟨some (lbl B 4), s3, S3⟩ ∧
        S3 D = (decM a).1.map eIn.symm ∧ S3 C = bitsC (decM a).2.reverse ∧
        ∀ p, p ≠ D → p ≠ C → S3 p = [] := by
  have hFD : F ≠ (D : drv.K ⊕ B.K) := by intro h; unfold F D at h; cases h
  have hS0D : initStk eIn a D = a.map eIn.symm := Function.update_self _ _ _
  have hS0 : ∀ p, p ≠ D → initStk eIn a p = [] := fun p hp => by
    unfold initStk
    rw [Function.update_of_ne hp]
  obtain ⟨k, hk, s1, S1, hdec, hD1, hF1, hfr1⟩ :=
    dec_run eIn eOut a.length a le_rfl (initSc B) (initStk eIn a) hS0D
  have hS1C : S1 C = [] := by rw [hfr1 C dC_ne_D dC_ne_F]; exact hS0 C dC_ne_D
  have hS1F : S1 F = bitsF ((decM a).1.reverse) := by
    rw [hF1, hS0 F hFD, List.append_nil]
  -- the counter moves from `D` to `C`
  have hmDC := mv_run (Mc eIn eOut) D C dC_ne_D.symm eIn (show Bool → Phys drv B C from fun x => x)
    (fun s x => (s.1, x.map eIn, s.2.2)) (fun s => s.2.1.getD false) (lbl B 2) (lbl B 3) rfl
    (fun _ _ => rfl) (fun s b' h => by simp [h]) (S1 D) s1 S1 rfl
  -- the data moves from `F` back to `D`
  have hS2F : (Function.update (Function.update S1 D []) C
      (((S1 D).map ((show Bool → Phys drv B C from fun x => x) ∘ eIn)).reverse ++ S1 C)) F
      = bitsF ((decM a).1.reverse) := by
    rw [Function.update_of_ne dC_ne_F.symm, Function.update_of_ne hFD, hS1F]
  have hmFD := mv_run (Mc eIn eOut) F D hFD (fun x => x) (fun x => eIn.symm x)
    (fun s x => (s.1, x, s.2.2)) (fun s => eIn.symm (s.2.1.getD false)) (lbl B 3) (lbl B 4) rfl
    (fun s x => by cases x <;> rfl) (fun s b' h => by simp [h]) (bitsF ((decM a).1.reverse))
    (s1.1, none, s1.2.2) _ hS2F
  have hlS1D : (S1 D).length = (decM a).2.length := by
    calc (S1 D).length = ((decM a).2.map eIn.symm).length := by rw [hD1]; rfl
      _ = (decM a).2.length := List.length_map _
  have hlB : (bitsF (B := B) ((decM a).1.reverse)).length = (decM a).1.length := by
    show (decM a).1.reverse.length = _
    rw [List.length_reverse]
  have hS2D : (Function.update (Function.update S1 D []) C
      (((S1 D).map ((show Bool → Phys drv B C from fun x => x) ∘ eIn)).reverse ++ S1 C)) D = [] := by
    rw [Function.update_of_ne dC_ne_D.symm, Function.update_self]
  refine ⟨(bitsF ((decM a).1.reverse)).length + 1 + ((S1 D).length + 1 + k), ?_, _, _,
    run_trans _ (run_trans _ hdec hmDC) hmFD, ?_, ?_, ?_⟩
  · omega
  · rw [Function.update_self, hS2D, List.append_nil]
    exact bitsF_map_rev eIn.symm (decM a).1
  · rw [Function.update_of_ne dC_ne_D, Function.update_of_ne dC_ne_F, Function.update_self, hS1C,
      hD1, List.append_nil]
    simp [bitsC, Function.comp_def, List.map_map]
    exact congrArg List.reverse (map_idC (B := B) _)
  · intro p hpD hpC
    rw [Function.update_of_ne hpD]
    by_cases hpF : p = F
    · subst hpF
      rw [Function.update_self]
    · rw [Function.update_of_ne hpF, Function.update_of_ne hpC, Function.update_of_ne hpD,
        hfr1 p hpD hpF, hS0 p hpD]

/-- The whole run on any input `a`: decode, move, then the rounds. -/
theorem main_run (eIn : B.Γ B.k₀ ≃ Bool) (eOut : B.Γ B.k₁ ≃ Bool) (g : List Bool → List Bool)
    (hlen : ∀ z, (g z).length = z.length + 1) (q : Polynomial ℕ)
    (hbody : ∀ w : List Bool, ∃ tb, tb ≤ q.eval w.length ∧
      (flip bind (TM2.step B.m))^[tb] (some (initList B (w.map eIn.symm))) =
        some (haltList B ((g w).map eOut.symm)))
    (a : List Bool) :
    ∃ t, t ≤ a.length * (q.eval (2 * a.length) + 4 * a.length + 8) + 3 * a.length + 6 ∧
      ∃ S' : (∀ p, List (Phys drv B p)),
        Run (Mc eIn eOut) t ⟨some (lbl B 0), initSc B, initStk eIn a⟩ ⟨none, initSc B, S'⟩ ∧
        S' D = ((g^[(decM a).2.length]) (decM a).1).map eIn.symm ∧
        ∀ p, p ≠ D → S' p = [] := by
  obtain ⟨t0, ht0, s3, S3, hR0, hD3, hC3, hO3⟩ := pre_rounds eIn eOut g hlen a
  obtain ⟨t3, ht3, S', hR3, hD', hO'⟩ := rounds_run eIn eOut g hlen q hbody (decM a).2.length
    (decM a).1 s3 S3 (decM a).2.reverse (by simp) hD3 hC3 hO3
  refine ⟨t3 + t0, ?_, S', run_trans _ hR0 hR3, hD', hO'⟩
  have hw := decM_len a.length a le_rfl
  have hpoly : q.eval ((decM a).1.length + (decM a).2.length) ≤ q.eval (2 * a.length) :=
    poly_mono q _ _ (by omega)
  have hmul : (decM a).2.length * (q.eval ((decM a).1.length + (decM a).2.length) +
      2 * ((decM a).1.length + (decM a).2.length) + 8) ≤
      a.length * (q.eval (2 * a.length) + 4 * a.length + 8) :=
    Nat.mul_le_mul (by omega) (by omega)
  linarith

end Main

section Final

/-- The time polynomial of the loop machine, from the time `q` of the body. -/
noncomputable def loopTime (q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X * (q.comp (Polynomial.C 2 * Polynomial.X) + Polynomial.C 4 * Polynomial.X +
    Polynomial.C 8) + Polynomial.C 3 * Polynomial.X + Polynomial.C 6

theorem loopTime_eval (q : Polynomial ℕ) (n : ℕ) :
    (loopTime q).eval n = n * (q.eval (2 * n) + 4 * n + 8) + 3 * n + 6 := by
  simp only [loopTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_comp]

theorem main : ∀ g : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) g) →
    (∀ z : List Bool, (g z).length = z.length + 1) →
    ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ z : List Bool, ∀ k : ℕ, T (MPP.PvsNP.pair z (List.replicate k false)) = g^[k] z := by
  intro g hg hlen
  obtain ⟨hs⟩ := hg
  haveI := hs.tm.kFin
  haveI := hs.tm.ΛFin
  haveI := hs.tm.σFin
  haveI := hs.tm.Γk₀Fin
  have hbody : ∀ w : List Bool, ∃ tb, tb ≤ hs.time.eval w.length ∧
      (flip bind (TM2.step hs.tm.m))^[tb] (some (initList hs.tm (w.map hs.inputAlphabet.symm))) =
        some (haltList hs.tm ((g w).map hs.outputAlphabet.symm)) := by
    intro w
    have H := hs.outputsFun w
    exact ⟨H.steps, H.steps_le_m, H.evals_in_steps⟩
  have hTM : ∀ a : List Bool, Nonempty (TM2OutputsInTime
      (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
      (List.map hs.inputAlphabet.invFun (id a))
      (Option.some (List.map hs.inputAlphabet.invFun (id ((g^[(decM a).2.length]) (decM a).1))))
      ((loopTime hs.time).eval (id a).length)) := by
    intro a
    obtain ⟨t, ht, S', hrun, hD, hO⟩ :=
      main_run (B := hs.tm) hs.inputAlphabet hs.outputAlphabet g hlen hs.time hbody a
    have hinit : initList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
        (List.map hs.inputAlphabet.invFun (id a)) =
        ⟨some (lbl hs.tm 0), initSc hs.tm, initStk hs.inputAlphabet a⟩ := by
      have hstk : (initList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
          (List.map hs.inputAlphabet.invFun (id a))).stk = initStk hs.inputAlphabet a := by
        funext p
        by_cases hp : p = D
        · subst hp
          exact (initList_stk_self' _ _).trans (by unfold initStk; rw [Function.update_self]; rfl)
        · exact (initList_stk_ne' _ _ hp).trans (initStk_ne (B := hs.tm) hs.inputAlphabet a hp).symm
      calc initList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
            (List.map hs.inputAlphabet.invFun (id a))
          = ⟨some (lbl hs.tm 0), initSc hs.tm, (initList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
            (List.map hs.inputAlphabet.invFun (id a))).stk⟩ := rfl
        _ = ⟨some (lbl hs.tm 0), initSc hs.tm, initStk hs.inputAlphabet a⟩ := by rw [hstk]
    have hhalt : haltList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
        (List.map hs.inputAlphabet.invFun (id ((g^[(decM a).2.length]) (decM a).1))) =
        ⟨none, initSc hs.tm, S'⟩ := by
      have hstk : (haltList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
          (List.map hs.inputAlphabet.invFun (id ((g^[(decM a).2.length]) (decM a).1)))).stk = S' := by
        funext p
        by_cases hp : p = D
        · subst hp
          exact (haltList_stk_self' _ _).trans hD.symm
        · exact (haltList_stk_ne' _ _ hp).trans (hO p hp).symm
      calc haltList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
            (List.map hs.inputAlphabet.invFun (id ((g^[(decM a).2.length]) (decM a).1)))
          = ⟨none, initSc hs.tm, (haltList (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet)
            (List.map hs.inputAlphabet.invFun (id ((g^[(decM a).2.length]) (decM a).1)))).stk⟩ := rfl
        _ = ⟨none, initSc hs.tm, S'⟩ := by rw [hstk]
    refine ⟨⟨⟨t, ?_⟩, ?_⟩⟩
    · refine (congrArg (fun c => (flip bind (loopTM hs.tm hs.inputAlphabet hs.outputAlphabet).step)^[t]
        (some c)) hinit).trans (hrun.trans ?_)
      exact congrArg some hhalt.symm
    · rw [loopTime_eval]
      simp only [id]
      omega
  refine ⟨fun a => (g^[(decM a).2.length]) (decM a).1, ⟨{
    tm := loopTM hs.tm hs.inputAlphabet hs.outputAlphabet
    inputAlphabet := hs.inputAlphabet
    outputAlphabet := hs.inputAlphabet
    time := loopTime hs.time
    outputsFun := fun a => Classical.choice (hTM a) }⟩, ?_⟩
  intro z k
  show (g^[(decM (MPP.PvsNP.pair z (List.replicate k false))).2.length])
    (decM (MPP.PvsNP.pair z (List.replicate k false))).1 = g^[k] z
  rw [decM_pair]
  simp

end Final

end MPP.Solutions.Pnp066
