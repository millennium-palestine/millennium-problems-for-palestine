import Mathlib

namespace MPP.Solutions.Pnp006

open Turing

section Defs

variable (A B : FinTM2)

/-- The physical stack carrying the `k`-th stack of `B`. -/
def psi (k : B.K) : A.K ⊕ B.K :=
  if k = B.k₀ then Sum.inl A.k₁ else Sum.inr k

/-- The physical alphabet: `A`'s alphabets on the left, `B`'s on the right. -/
def Phys : A.K ⊕ B.K → Type :=
  Sum.elim A.Γ B.Γ

/-- Identifies the alphabet of the physical stack `psi k` with `B.Γ k`. -/
def eps (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (k : B.K) : Phys A B (psi A B k) ≃ B.Γ k :=
  if h : k = B.k₀ then
    (Equiv.cast (by simp [Phys, psi, h])).trans (e.trans (Equiv.cast (by rw [h])))
  else Equiv.cast (by simp [Phys, psi, h])

/-- An embedding of the statements of a machine `T` into the composed machine. -/
structure Emb (Λc σc : Type) (T : FinTM2) where
  ι : T.K → A.K ⊕ B.K
  ε : (k : T.K) → Phys A B (ι k) ≃ T.Γ k
  lab : T.Λ → Λc
  π : σc → T.σ
  set : T.σ → σc → σc
  haltTo : Λc
  ι_inj : Function.Injective ι
  set_π : ∀ s, set (π s) s = s
  π_set : ∀ v s, π (set v s) = v
  set_set : ∀ v w s, set v (set w s) = set v s

variable {A B}

/-- Translation of a statement of `T` into the composed machine. -/
def trS {Λc σc : Type} {T : FinTM2} (E : Emb A B Λc σc T) :
    TM2.Stmt T.Γ T.Λ T.σ → TM2.Stmt (Phys A B) Λc σc
  | TM2.Stmt.push k f q => TM2.Stmt.push (E.ι k) (fun s => (E.ε k).symm (f (E.π s))) (trS E q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (E.ι k) (fun s x => E.set (f (E.π s) (x.map (E.ε k))) s) (trS E q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (E.ι k) (fun s x => E.set (f (E.π s) (x.map (E.ε k))) s) (trS E q)
  | TM2.Stmt.load a q => TM2.Stmt.load (fun s => E.set (a (E.π s)) s) (trS E q)
  | TM2.Stmt.branch p q₁ q₂ =>
      TM2.Stmt.branch (fun s => p (E.π s)) (trS E q₁) (trS E q₂)
  | TM2.Stmt.goto l => TM2.Stmt.goto (fun s => E.lab (l (E.π s)))
  | TM2.Stmt.halt => TM2.Stmt.goto (fun _ => E.haltTo)

end Defs

section Sim

variable {A B}

theorem head_map_symm {α β : Type} (e : α ≃ β) (S : List β) :
    ((S.map e.symm).head?).map e = S.head? := by
  cases S <;> simp

theorem tail_map_symm {α β : Type} (e : α ≃ β) (S : List β) :
    (S.map e.symm).tail = S.tail.map e.symm := by
  cases S <;> simp

variable {Λc σc : Type} {T : FinTM2}

/-- The stacks of the composed machine carry the stacks of `T` under `E`. -/
def Inv (E : Emb A B Λc σc T) (S : ∀ k, List (T.Γ k)) (P : ∀ p, List (Phys A B p)) : Prop :=
  ∀ k, P (E.ι k) = (S k).map (E.ε k).symm

/-- The label reached by a step: `none` (halting in `T`) goes to `haltTo`. -/
def liftL (E : Emb A B Λc σc T) : Option T.Λ → Option Λc
  | none => some E.haltTo
  | some l => some (E.lab l)

theorem Inv_update_of_ne (E : Emb A B Λc σc T) {S : ∀ k, List (T.Γ k)}
    {P : ∀ p, List (Phys A B p)} (hI : Inv E S P) {k : T.K} {x : List (T.Γ k)}
    {y : List (Phys A B (E.ι k))} (hy : y = (x.map (E.ε k).symm)) :
    Inv E (Function.update S k x) (Function.update P (E.ι k) y) := by
  intro k'
  by_cases h : k' = k
  · subst h
    rw [Function.update_self, Function.update_self, hy]
  · have h' : E.ι k' ≠ E.ι k := fun h2 => h (E.ι_inj h2)
    rw [Function.update_of_ne h', Function.update_of_ne h]
    exact hI k'

theorem stepAux_trS (E : Emb A B Λc σc T) (q : TM2.Stmt T.Γ T.Λ T.σ) :
    ∀ (v : T.σ) (S : ∀ k, List (T.Γ k)) (s : σc) (P : ∀ p, List (Phys A B p)),
      E.π s = v → Inv E S P →
      ∃ P', TM2.stepAux (trS E q) s P =
          ⟨liftL E (TM2.stepAux q v S).l, E.set (TM2.stepAux q v S).var s, P'⟩ ∧
        Inv E (TM2.stepAux q v S).stk P' ∧
        ∀ p, (∀ k, p ≠ E.ι k) → P' p = P p := by
  induction q with
  | push k f q ih =>
    intro v S s P hv hI
    subst hv
    obtain ⟨P', h1, h2, h3⟩ := ih (E.π s) (Function.update S k (f (E.π s) :: S k)) s
      (Function.update P (E.ι k) ((E.ε k).symm (f (E.π s)) :: P (E.ι k)))
      rfl (Inv_update_of_ne E hI (y := (E.ε k).symm (f (E.π s)) :: P (E.ι k))
        (x := f (E.π s) :: S k) (by simp [hI k]))
    refine ⟨P', ?_, h2, ?_⟩
    · simpa [trS, TM2.stepAux] using h1
    · intro p hp
      rw [h3 p hp, Function.update_of_ne (hp (k)), ]
  | peek k f q ih =>
    intro v S s P hv hI
    subst hv
    have hx : ((P (E.ι k)).head?).map (E.ε k) = (S k).head? := by
      rw [hI k]; exact head_map_symm (E.ε k) (S k)
    obtain ⟨P', h1, h2, h3⟩ := ih (f (E.π s) (S k).head?) S
      (E.set (f (E.π s) (((P (E.ι k)).head?).map (E.ε k))) s) P
      (by rw [E.π_set, hx]) hI
    refine ⟨P', ?_, h2, h3⟩
    simp only [trS, TM2.stepAux, E.set_set] at h1 ⊢
    exact h1
  | pop k f q ih =>
    intro v S s P hv hI
    subst hv
    have hx : ((P (E.ι k)).head?).map (E.ε k) = (S k).head? := by
      rw [hI k]; exact head_map_symm (E.ε k) (S k)
    have hI' := Inv_update_of_ne E hI (x := (S k).tail) (y := (P (E.ι k)).tail)
      (by rw [hI k, tail_map_symm])
    obtain ⟨P', h1, h2, h3⟩ := ih (f (E.π s) (S k).head?) (Function.update S k (S k).tail)
      (E.set (f (E.π s) (((P (E.ι k)).head?).map (E.ε k))) s)
      (Function.update P (E.ι k) (P (E.ι k)).tail)
      (by rw [E.π_set, hx]) hI'
    refine ⟨P', ?_, h2, ?_⟩
    · simp only [trS, TM2.stepAux, E.set_set] at h1 ⊢
      exact h1
    · intro p hp
      rw [h3 p hp, Function.update_of_ne (hp k)]
  | load a q ih =>
    intro v S s P hv hI
    subst hv
    obtain ⟨P', h1, h2, h3⟩ := ih (a (E.π s)) S (E.set (a (E.π s)) s) P
      (by rw [E.π_set]) hI
    refine ⟨P', ?_, h2, h3⟩
    simp only [trS, TM2.stepAux, E.set_set] at h1 ⊢
    exact h1
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro v S s P hv hI
    subst hv
    cases hb : p (E.π s)
    · obtain ⟨P', h1, h2, h3⟩ := ih₂ (E.π s) S s P rfl hI
      refine ⟨P', ?_, ?_, h3⟩
      · simp only [trS, TM2.stepAux, hb] at h1 ⊢
        exact h1
      · simpa [TM2.stepAux, hb] using h2
    · obtain ⟨P', h1, h2, h3⟩ := ih₁ (E.π s) S s P rfl hI
      refine ⟨P', ?_, ?_, h3⟩
      · simp only [trS, TM2.stepAux, hb] at h1 ⊢
        exact h1
      · simpa [TM2.stepAux, hb] using h2
  | goto l =>
    intro v S s P hv hI
    subst hv
    refine ⟨P, ?_, hI, fun _ _ => rfl⟩
    simp [trS, TM2.stepAux, liftL, E.set_π]
  | halt =>
    intro v S s P hv hI
    subst hv
    refine ⟨P, ?_, hI, fun _ _ => rfl⟩
    simp [trS, TM2.stepAux, liftL, E.set_π]

end Sim

section Machine

variable (A B : FinTM2) [Fintype A.K] [Fintype B.K] [Fintype A.Λ] [Fintype B.Λ]
  [Fintype A.σ] [Fintype B.σ] [Fintype (A.Γ A.k₀)]

theorem psi_injective : Function.Injective (psi A B) := by
  intro k k' h
  unfold psi at h
  by_cases h1 : k = B.k₀ <;> by_cases h2 : k' = B.k₀ <;> simp_all

/-- Number of physical stacks, and an enumeration of them for the cleanup phase. -/
noncomputable def enumK : (A.K ⊕ B.K) ≃ Fin (Fintype.card (A.K ⊕ B.K)) :=
  Fintype.equivFin _

/-- Labels: those of `A`, those of `B`, and one cleanup label per position `i`
(the label `Fin.last` is the final step). -/
abbrev Lc := A.Λ ⊕ B.Λ ⊕ Fin (Fintype.card (A.K ⊕ B.K) + 1)

/-- States: `A`'s state, `B`'s state, and a flag used by the cleanup loops. -/
abbrev Sc := A.σ × B.σ × Bool

/-- The initial state of the composed machine. -/
def initSc : Sc A B := (A.initialState, B.initialState, false)

/-- The embedding of `A`: its stacks are the left ones, its labels are on the left. -/
def embA : Emb A B (Lc A B) (Sc A B) A where
  ι := Sum.inl
  ε := fun _ => Equiv.refl _
  lab := Sum.inl
  π := Prod.fst
  set := fun v s => (v, s.2)
  haltTo := Sum.inr (Sum.inl B.main)
  ι_inj := Sum.inl_injective
  set_π := fun _ => rfl
  π_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl

/-- The embedding of `B`: its stacks are `psi`, glued through `e`. -/
def embB (e : A.Γ A.k₁ ≃ B.Γ B.k₀) : Emb A B (Lc A B) (Sc A B) B where
  ι := psi A B
  ε := eps A B e
  lab := fun l => Sum.inr (Sum.inl l)
  π := fun s => s.2.1
  set := fun v s => (s.1, v, s.2.2)
  haltTo := Sum.inr (Sum.inr 0)
  ι_inj := psi_injective A B
  set_π := fun _ => rfl
  π_set := fun _ _ => rfl
  set_set := fun _ _ _ => rfl

/-- Cleanup step `i`: empty the physical stack number `i` (unless it is the output stack),
looping while it is non-empty, then go to step `i + 1`. Step `Fin.last` halts with the
composed initial state. -/
noncomputable def cleanStmt (i : Fin (Fintype.card (A.K ⊕ B.K) + 1)) :
    TM2.Stmt (Phys A B) (Lc A B) (Sc A B) :=
  if h : i.val < Fintype.card (A.K ⊕ B.K) then
    if (enumK A B).symm ⟨i.val, h⟩ = psi A B B.k₁ then
      TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr (i + 1)))
    else
      TM2.Stmt.pop ((enumK A B).symm ⟨i.val, h⟩) (fun s x => (s.1, s.2.1, x.isSome))
        (TM2.Stmt.branch (fun s => s.2.2) (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr i)))
          (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr (i + 1)))))
  else TM2.Stmt.load (fun _ => initSc A B) TM2.Stmt.halt

/-- The statements of the composed machine. -/
noncomputable def Mc (e : A.Γ A.k₁ ≃ B.Γ B.k₀) :
    Lc A B → TM2.Stmt (Phys A B) (Lc A B) (Sc A B)
  | Sum.inl l => trS (embA A B) (A.m l)
  | Sum.inr (Sum.inl l) => trS (embB A B e) (B.m l)
  | Sum.inr (Sum.inr i) => cleanStmt A B i

/-- The composed machine: `A` then `B`, with cleanup. Its input is `A`'s input and its
output is `B`'s output (on the stack `psi B.k₁`). -/
noncomputable def compTM (e : A.Γ A.k₁ ≃ B.Γ B.k₀) : FinTM2 where
  K := A.K ⊕ B.K
  k₀ := Sum.inl A.k₀
  k₁ := psi A B B.k₁
  Γ := Phys A B
  Λ := Lc A B
  main := Sum.inl A.main
  σ := Sc A B
  initialState := initSc A B
  m := Mc A B e
  Γk₀Fin := (inferInstance : Fintype (A.Γ A.k₀))

/-- A run of `k` steps of `T` is a run of `k` steps of the composed machine, as long as the
composed machine is `T`'s statements (through `E`). -/
theorem iter_sim (e : A.Γ A.k₁ ≃ B.Γ B.k₀) {T : FinTM2} (E : Emb A B (Lc A B) (Sc A B) T)
    (hm : ∀ l, Mc A B e (E.lab l) = trS E (T.m l)) (s0 : Sc A B) :
    ∀ (k : ℕ) (c0 c : TM2.Cfg T.Γ T.Λ T.σ) (P0 : ∀ p, List (Phys A B p)),
      (flip bind (TM2.step T.m))^[k] (some c0) = some c → Inv E c0.stk P0 →
      ∃ P, (flip bind (TM2.step (Mc A B e)))^[k] (some ⟨liftL E c0.l, E.set c0.var s0, P0⟩) =
            some ⟨liftL E c.l, E.set c.var s0, P⟩ ∧ Inv E c.stk P ∧
          ∀ p, (∀ k', p ≠ E.ι k') → P p = P0 p := by
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
    cases hk : (flip bind (TM2.step T.m))^[k] (some c0) with
    | none =>
      rw [hk] at h
      simp [flip] at h
    | some ck =>
      rw [hk] at h
      have h' : TM2.step T.m ck = some c := by simpa [flip] using h
      obtain ⟨P1, hit, hI1, hfr1⟩ := ih c0 ck P0 hk hI
      rcases ck with ⟨_ | l, v, S⟩
      · simp [TM2.step] at h'
      · have hc : TM2.stepAux (T.m l) v S = c := by simpa [TM2.step] using h'
        subst hc
        obtain ⟨P', hr, hI', hfr'⟩ :=
          stepAux_trS E (T.m l) v S (E.set v s0) P1 (E.π_set _ _) hI1
        refine ⟨P', ?_, hI', fun p hp => (hfr' p hp).trans (hfr1 p hp)⟩
        rw [Function.iterate_succ_apply', hit]
        show TM2.step (Mc A B e) ⟨some (E.lab l), E.set v s0, P1⟩ = _
        show some (TM2.stepAux (Mc A B e (E.lab l)) (E.set v s0) P1) = _
        rw [hm, hr, E.set_set]

theorem cleanStmt_out (i : Fin (Fintype.card (A.K ⊕ B.K) + 1)) (h : i.val < Fintype.card (A.K ⊕ B.K))
    (hO : (enumK A B).symm ⟨i.val, h⟩ = psi A B B.k₁) :
    cleanStmt A B i = TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr (i + 1))) := by
  unfold cleanStmt
  rw [dif_pos h, if_pos hO]

theorem cleanStmt_pop (i : Fin (Fintype.card (A.K ⊕ B.K) + 1)) (h : i.val < Fintype.card (A.K ⊕ B.K))
    (hO : (enumK A B).symm ⟨i.val, h⟩ ≠ psi A B B.k₁) :
    cleanStmt A B i = TM2.Stmt.pop ((enumK A B).symm ⟨i.val, h⟩)
      (fun s x => (s.1, s.2.1, x.isSome))
      (TM2.Stmt.branch (fun s => s.2.2) (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr i)))
        (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr (i + 1))))) := by
  unfold cleanStmt
  rw [dif_pos h, if_neg hO]

theorem cleanStmt_last (i : Fin (Fintype.card (A.K ⊕ B.K) + 1)) (h : ¬ i.val < Fintype.card (A.K ⊕ B.K)) :
    cleanStmt A B i = TM2.Stmt.load (fun _ => initSc A B) TM2.Stmt.halt := by
  unfold cleanStmt
  rw [dif_neg h]

/-- Emptying one physical stack: `p` holds `L`; the loop takes `L.length + 1` steps and
leaves `p` empty. -/
theorem clean_loop (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (i : Fin (Fintype.card (A.K ⊕ B.K) + 1))
    (p : A.K ⊕ B.K)
    (hcl : cleanStmt A B i = TM2.Stmt.pop p (fun s x => (s.1, s.2.1, x.isSome))
      (TM2.Stmt.branch (fun s => s.2.2) (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr i)))
        (TM2.Stmt.goto (fun _ => Sum.inr (Sum.inr (i + 1)))))) :
    ∀ (L : List (Phys A B p)) (P : ∀ q, List (Phys A B q)) (s : Sc A B), P p = L →
      ∃ s', (flip bind (TM2.step (Mc A B e)))^[L.length + 1]
          (some ⟨some (Sum.inr (Sum.inr i)), s, P⟩) =
        some ⟨some (Sum.inr (Sum.inr (i + 1))), s', Function.update P p []⟩ := by
  intro L
  induction L with
  | nil =>
    intro P s hP
    refine ⟨(s.1, s.2.1, false), ?_⟩
    have hstep : TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr i)), s, P⟩ =
        some ⟨some (Sum.inr (Sum.inr (i + 1))), (s.1, s.2.1, false), Function.update P p []⟩ := by
      show some (TM2.stepAux (cleanStmt A B i) s P) = _
      rw [hcl]
      simp [TM2.stepAux, hP]
    simp only [List.length_nil, zero_add, Function.iterate_one]
    exact hstep
  | cons a L ih =>
    intro P s hP
    have hstep : TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr i)), s, P⟩ =
        some ⟨some (Sum.inr (Sum.inr i)), (s.1, s.2.1, true), Function.update P p L⟩ := by
      show some (TM2.stepAux (cleanStmt A B i) s P) = _
      rw [hcl]
      simp [TM2.stepAux, hP]
    obtain ⟨s', hs'⟩ := ih (Function.update P p L) (s.1, s.2.1, true)
      (by rw [Function.update_self])
    rw [Function.update_idem] at hs'
    refine ⟨s', ?_⟩
    rw [List.length_cons, Function.iterate_succ_apply]
    show (flip bind (TM2.step (Mc A B e)))^[L.length + 1]
      (TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr i)), s, P⟩) = _
    rw [hstep]
    exact hs'

theorem sum_update_zero_add {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (a : ι) :
    ∑ x, Function.update f a 0 x + f a = ∑ x, f x := by
  have h := Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)
  rw [Finset.sum_update_of_mem (Finset.mem_univ a), Finset.sdiff_singleton_eq_erase, ← h]
  omega

theorem fin_val_add_one {n : ℕ} (i : Fin (n + 1)) (h : i.val < n) : (i + 1).val = i.val + 1 := by
  apply Fin.val_add_one_of_lt
  rw [Fin.lt_iff_val_lt_val, Fin.val_last]
  exact h

theorem eq_symm_of_val {ι : Type} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι)) {x : ι}
    {n : ℕ} (hn : n < Fintype.card ι) (hv : (e x).val = n) :
    x = e.symm ⟨n, hn⟩ := by
  rw [Equiv.eq_symm_apply]
  exact Fin.ext hv

/-- The cleanup chain from label `i` on: it empties every physical stack with position at
least `i`, except the output stack, and reaches the final label. -/
theorem clean_chain (e : A.Γ A.k₁ ≃ B.Γ B.k₀) : ∀ (m : ℕ) (i : Fin (Fintype.card (A.K ⊕ B.K) + 1)),
    i.val + m = Fintype.card (A.K ⊕ B.K) → ∀ (P : ∀ q, List (Phys A B q)) (s : Sc A B),
    ∃ (k : ℕ) (s' : Sc A B) (P' : ∀ q, List (Phys A B q)),
      (flip bind (TM2.step (Mc A B e)))^[k] (some ⟨some (Sum.inr (Sum.inr i)), s, P⟩) =
        some ⟨some (Sum.inr (Sum.inr (Fin.last _))), s', P'⟩ ∧
      (∀ q, i.val ≤ (enumK A B q).val → q ≠ psi A B B.k₁ → P' q = []) ∧
      (∀ q, (enumK A B q).val < i.val → P' q = P q) ∧
      P' (psi A B B.k₁) = P (psi A B B.k₁) ∧
      k ≤ (∑ q, (P q).length) + 2 * m + 1 := by
  intro m
  induction m with
  | zero =>
    intro i hi P s
    have hil : i = Fin.last _ := Fin.ext (by rw [Fin.val_last]; omega)
    subst hil
    refine ⟨0, s, P, rfl, ?_, fun _ _ => rfl, rfl, by omega⟩
    intro q hq _
    have := (enumK A B q).isLt
    rw [Fin.val_last] at hq
    omega
  | succ m ih =>
    intro i hi P s
    have hi' : i.val < Fintype.card (A.K ⊕ B.K) := by omega
    have hv : (i + 1).val = i.val + 1 := fin_val_add_one i hi'
    by_cases hO : (enumK A B).symm ⟨i.val, hi'⟩ = psi A B B.k₁
    · have hstep : TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr i)), s, P⟩ =
          some ⟨some (Sum.inr (Sum.inr (i + 1))), s, P⟩ := by
        show some (TM2.stepAux (cleanStmt A B i) s P) = _
        rw [cleanStmt_out A B i hi' hO]
        simp [TM2.stepAux]
      obtain ⟨k, s', P', hit, hA, hB, hC, hD⟩ := ih (i + 1) (by omega) P s
      refine ⟨k + 1, s', P', ?_, ?_, fun q hq => hB q (by omega), hC, by omega⟩
      · rw [Function.iterate_succ_apply]
        show (flip bind (TM2.step (Mc A B e)))^[k]
          (TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr i)), s, P⟩) = _
        rw [hstep]
        exact hit
      · intro q hq hqO
        rcases Nat.lt_or_ge (enumK A B q).val (i.val + 1) with h | h
        · exfalso
          have hq' : q = (enumK A B).symm ⟨i.val, hi'⟩ := eq_symm_of_val (enumK A B) hi' (by omega)
          exact hqO (hq'.trans hO)
        · exact hA q (by omega) hqO
    · have hcl := cleanStmt_pop A B i hi' hO
      obtain ⟨s1, hs1⟩ := clean_loop A B e i ((enumK A B).symm ⟨i.val, hi'⟩) hcl
        (P _) P s rfl
      obtain ⟨k, s', P', hit, hA, hB, hC, hbd⟩ :=
        ih (i + 1) (by omega) (Function.update P ((enumK A B).symm ⟨i.val, hi'⟩) []) s1
      have hsum : ∑ q, (Function.update P ((enumK A B).symm ⟨i.val, hi'⟩) [] q).length
          + ((P ((enumK A B).symm ⟨i.val, hi'⟩)).length) = ∑ q, (P q).length := by
        have hf : (fun q => (Function.update P ((enumK A B).symm ⟨i.val, hi'⟩) [] q).length) =
            Function.update (fun q => (P q).length) ((enumK A B).symm ⟨i.val, hi'⟩) 0 := by
          funext q
          by_cases h : q = (enumK A B).symm ⟨i.val, hi'⟩
          · subst h; simp
          · simp [Function.update_of_ne h]
        rw [hf]
        exact sum_update_zero_add (fun q => (P q).length) _
      have hne : ∀ q, (enumK A B q).val < i.val → q ≠ (enumK A B).symm ⟨i.val, hi'⟩ := by
        intro q hq hqp
        subst hqp
        simp at hq
      refine ⟨k + ((P ((enumK A B).symm ⟨i.val, hi'⟩)).length + 1), s', P', ?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.iterate_add_apply, hs1]
        exact hit
      · intro q hq hqO
        rcases Nat.lt_or_ge (enumK A B q).val (i.val + 1) with h | h
        · have hq' : q = (enumK A B).symm ⟨i.val, hi'⟩ := eq_symm_of_val (enumK A B) hi' (by omega)
          subst hq'
          rw [hB _ (by omega)]
          simp
        · exact hA q (by omega) hqO
      · intro q hq
        rw [hB q (by omega), Function.update_of_ne (hne q hq)]
      · rw [hC, Function.update_of_ne (fun h => hO h.symm)]
      · omega

/-- Number of pushes in a statement (an upper bound on the growth of the stacks in one step). -/
def pushCount {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | TM2.Stmt.push _ _ q => pushCount q + 1
  | TM2.Stmt.peek _ _ q => pushCount q
  | TM2.Stmt.pop _ _ q => pushCount q
  | TM2.Stmt.load _ q => pushCount q
  | TM2.Stmt.branch _ q₁ q₂ => pushCount q₁ + pushCount q₂
  | TM2.Stmt.goto _ => 0
  | TM2.Stmt.halt => 0

theorem sum_update_len {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k : K) (x : List (Γ k)) :
    ∑ j, (Function.update S k x j).length + (S k).length = ∑ j, (S j).length + x.length := by
  have hf : (fun j => (Function.update S k x j).length) =
      Function.update (fun j => (S j).length) k x.length := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  have := sum_update_zero_add (fun j => (S j).length) k
  have h2 : ∑ j, (Function.update S k x j).length = ∑ j, Function.update (fun j => (S j).length) k x.length j := by
    rw [hf]
  rw [h2]
  have h3 := Finset.add_sum_erase Finset.univ (fun j => (S j).length) (Finset.mem_univ k)
  have h4 := Finset.sum_update_of_mem (Finset.mem_univ k) (fun j => (S j).length) (x.length)
  rw [Finset.sdiff_singleton_eq_erase] at h4
  omega

theorem total_stepAux {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (S : ∀ k, List (Γ k)),
    ∑ k, ((TM2.stepAux q v S).stk k).length ≤ ∑ k, (S k).length + pushCount q := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [TM2.stepAux, pushCount]
    have h1 := ih v (Function.update S k (f v :: S k))
    have h2 := sum_update_len S k (f v :: S k)
    simp only [List.length_cons] at h2
    omega
  | peek k f q ih =>
    intro v S
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [TM2.stepAux, pushCount]
    have h1 := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have h2 := sum_update_len S k (S k).tail
    have h3 : (S k).tail.length ≤ (S k).length := by
      rw [List.length_tail]; omega
    omega
  | load a q ih =>
    intro v S
    simp only [TM2.stepAux, pushCount]
    exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [TM2.stepAux, pushCount]
    cases p v
    · have := ih₂ v S
      simp only [cond_false]
      omega
    · have := ih₁ v S
      simp only [cond_true]
      omega
  | goto l =>
    intro v S
    simp [TM2.stepAux, pushCount]
  | halt =>
    intro v S
    simp [TM2.stepAux, pushCount]

/-- Bound on the number of pushes of one step of the composed machine. -/
noncomputable def pushBound (e : A.Γ A.k₁ ≃ B.Γ B.k₀) : ℕ :=
  ∑ l, pushCount (Mc A B e l)

theorem total_iter (e : A.Γ A.k₁ ≃ B.Γ B.k₀) : ∀ (k : ℕ)
    (c0 c : TM2.Cfg (Phys A B) (Lc A B) (Sc A B)),
    (flip bind (TM2.step (Mc A B e)))^[k] (some c0) = some c →
    ∑ q, (c.stk q).length ≤ ∑ q, (c0.stk q).length + pushBound A B e * k := by
  intro k
  induction k with
  | zero =>
    intro c0 c h
    simp only [Function.iterate_zero_apply] at h
    cases h
    simp
  | succ k ih =>
    intro c0 c h
    rw [Function.iterate_succ_apply'] at h
    cases hk : (flip bind (TM2.step (Mc A B e)))^[k] (some c0) with
    | none =>
      rw [hk] at h
      simp [flip] at h
    | some ck =>
      rw [hk] at h
      have h' : TM2.step (Mc A B e) ck = some c := by simpa [flip] using h
      have hI := ih c0 ck hk
      rcases ck with ⟨_ | l, v, S⟩
      · simp [TM2.step] at h'
      · have hc : TM2.stepAux (Mc A B e l) v S = c := by simpa [TM2.step] using h'
        subst hc
        have hl : pushCount (Mc A B e l) ≤ pushBound A B e :=
          Finset.single_le_sum (f := fun l => pushCount (Mc A B e l)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ l)
        have hs := total_stepAux (Mc A B e l) v S
        dsimp only at hI ⊢
        rw [Nat.mul_succ]
        omega

theorem initList_stk_self' (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk tm.k₀ = s := by
  simp [initList]

theorem initList_stk_ne' (tm : FinTM2) (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := by
  simp [initList, h]

theorem haltList_stk_self' (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

theorem haltList_stk_ne' (tm : FinTM2) (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := by
  simp [haltList, h]

theorem sum_initList' (tm : FinTM2) [Fintype tm.K] [DecidableEq tm.K] (s : List (tm.Γ tm.k₀)) :
    ∑ q, ((initList tm s).stk q).length = s.length := by
  rw [Finset.sum_eq_single tm.k₀ (fun q _ hq => by rw [initList_stk_ne' tm s hq]; rfl)
    (fun h => absurd (Finset.mem_univ _) h), initList_stk_self']

/-- `psi B.k₀` is `A`'s output stack. -/
theorem psi_k0 : psi A B B.k₀ = Sum.inl A.k₁ := by
  unfold psi
  rw [if_pos rfl]

/-- Stacks at the index `psi B.k₀` are the stacks at `inl A.k₁`, transported along `psi_k0`. -/
theorem stack_transport (P : ∀ p, List (Phys A B p)) (q : A.K ⊕ B.K) (hq : q = Sum.inl A.k₁) :
    P q = (P (Sum.inl A.k₁)).map (fun x => cast (congrArg (Phys A B) hq).symm x) := by
  subst hq
  simp

theorem eps_k0_cast (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (x : Phys A B (Sum.inl A.k₁)) :
    eps A B e B.k₀ (cast (congrArg (Phys A B) (psi_k0 A B)).symm x) = e x := by
  unfold eps
  rw [dif_pos rfl]
  simp [Equiv.trans_apply, Equiv.cast_apply]
  rfl

/-- Start of the cleanup-free phase: the stacks of `A`'s run are on the left. -/
theorem init_inv (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (LA : List (A.Γ A.k₀)) :
    Inv (embA A B) (initList A LA).stk (initList (compTM A B e) LA).stk := by
  intro k
  by_cases hk : k = A.k₀
  · subst hk
    have h0 : (initList (compTM A B e) LA).stk (Sum.inl A.k₀) = LA :=
      initList_stk_self' (compTM A B e) LA
    change (initList (compTM A B e) LA).stk (Sum.inl A.k₀) = _
    rw [h0, initList_stk_self']
    exact (List.map_id' LA).symm
  · have h0 : (initList (compTM A B e) LA).stk (Sum.inl k) = [] :=
      initList_stk_ne' (compTM A B e) LA (k := Sum.inl k) (fun h => hk (Sum.inl.inj h))
    change (initList (compTM A B e) LA).stk (Sum.inl k) = _
    rw [h0, initList_stk_ne' A LA hk]
    rfl

theorem sum_init_comp (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (LA : List (A.Γ A.k₀)) :
    ∑ q : A.K ⊕ B.K, ((initList (compTM A B e) LA).stk q).length = LA.length :=
  @sum_initList' (compTM A B e) (inferInstance : Fintype (A.K ⊕ B.K))
    (inferInstance : DecidableEq (A.K ⊕ B.K)) LA

/-- The composed run: `A` on `LA`, then `B` on `A`'s output, then cleanup. -/
theorem comp_run (e : A.Γ A.k₁ ≃ B.Γ B.k₀) (LA : List (A.Γ A.k₀)) (LO : List (A.Γ A.k₁))
    (t1 : ℕ)
    (hA : (flip bind (TM2.step A.m))^[t1] (some (initList A LA)) = some (haltList A LO))
    (LB : List (B.Γ B.k₀)) (hLB : LB = LO.map e) (t2 : ℕ) (LOB : List (B.Γ B.k₁))
    (hB : (flip bind (TM2.step B.m))^[t2] (some (initList B LB)) = some (haltList B LOB)) :
    LO.length ≤ LA.length + pushBound A B e * t1 ∧
    ∃ kc : ℕ, (flip bind (TM2.step (Mc A B e)))^[t1 + t2 + kc]
        (some (initList (compTM A B e) LA)) =
          some (haltList (compTM A B e) (LOB.map (eps A B e B.k₁).symm)) ∧
      kc ≤ LA.length + pushBound A B e * (t1 + t2) + 2 * Fintype.card (A.K ⊕ B.K) + 2 := by
  subst hLB
  -- Phase 1: `A` runs on the composed machine.
  obtain ⟨P1, hit1, hI1, hfr1⟩ := iter_sim A B e (embA A B) (fun _ => rfl) (initSc A B) t1
    (initList A LA) (haltList A LO) (initList (compTM A B e) LA).stk hA (init_inv A B e LA)
  have hit1' : (flip bind (TM2.step (Mc A B e)))^[t1] (some (initList (compTM A B e) LA)) =
      some ⟨liftL (embA A B) (haltList A LO).l, (embA A B).set (haltList A LO).var (initSc A B),
        P1⟩ := hit1
  have hPl : P1 (Sum.inl A.k₁) = LO := by
    have h := hI1 A.k₁
    rw [haltList_stk_self'] at h
    exact h.trans (List.map_id' LO)
  -- Phase 2 invariant: `B`'s input is `A`'s output, through `psi`.
  have hInv2 : Inv (embB A B e) (initList B (LO.map e)).stk P1 := by
    intro k
    by_cases hk : k = B.k₀
    · subst hk
      show P1 (psi A B B.k₀) = _
      rw [stack_transport A B P1 (psi A B B.k₀) (psi_k0 A B), hPl, initList_stk_self',
        List.map_map]
      congr 1
      funext x
      exact (Equiv.eq_symm_apply _).mpr (eps_k0_cast A B e x)
    · show P1 (psi A B k) = _
      rw [initList_stk_ne' B (LO.map e) hk, List.map_nil]
      have hpk : psi A B k = Sum.inr k := by
        unfold psi
        rw [if_neg hk]
      show P1 (psi A B k) = ([] : List (Phys A B (psi A B k)))
      rw [hpk, hfr1 (Sum.inr k) (fun k' h => Sum.inr_ne_inl h)]
      exact initList_stk_ne' (compTM A B e) LA (fun h => Sum.inr_ne_inl h)
  -- Phase 2: `B` runs on the composed machine.
  obtain ⟨P2, hit2, hI2, hfr2⟩ := iter_sim A B e (embB A B e) (fun _ => rfl) (initSc A B) t2
    (initList B (LO.map e)) (haltList B LOB) P1 hB hInv2
  have hit2' : (flip bind (TM2.step (Mc A B e)))^[t2]
      (some ⟨liftL (embA A B) (haltList A LO).l, (embA A B).set (haltList A LO).var (initSc A B),
        P1⟩) =
      some ⟨liftL (embB A B e) (haltList B LOB).l, (embB A B e).set (haltList B LOB).var (initSc A B),
        P2⟩ := hit2
  -- Phase 3: cleanup.
  have hN : (0 : Fin (Fintype.card (A.K ⊕ B.K) + 1)).val + Fintype.card (A.K ⊕ B.K) =
      Fintype.card (A.K ⊕ B.K) := by
    rw [Fin.val_zero, zero_add]
  obtain ⟨kc0, s3, P3, hit3, hA3, hB3, hC3, hbd3⟩ :=
    clean_chain A B e (Fintype.card (A.K ⊕ B.K)) 0 hN P2 ((embB A B e).set (haltList B LOB).var (initSc A B))
  have hit3' : (flip bind (TM2.step (Mc A B e)))^[kc0]
      (some ⟨liftL (embB A B e) (haltList B LOB).l, (embB A B e).set (haltList B LOB).var (initSc A B),
        P2⟩) = some ⟨some (Sum.inr (Sum.inr (Fin.last _))), s3, P3⟩ := hit3
  have hlast : ¬ (Fin.last (Fintype.card (A.K ⊕ B.K))).val < Fintype.card (A.K ⊕ B.K) := by
    rw [Fin.val_last]
    exact lt_irrefl _
  have hfinal : TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr (Fin.last _))), s3, P3⟩ =
      some ⟨none, initSc A B, P3⟩ := by
    show some (TM2.stepAux (cleanStmt A B (Fin.last _)) s3 P3) = _
    rw [cleanStmt_last A B (Fin.last _) hlast]
    rfl
  -- The stacks at the end are exactly those of the halting configuration.
  have hP3 : P3 = (haltList (compTM A B e) (LOB.map (eps A B e B.k₁).symm)).stk := by
    funext q
    by_cases hq : q = psi A B B.k₁
    · subst hq
      rw [hC3]
      have h := hI2 B.k₁
      rw [haltList_stk_self'] at h
      exact h.trans (haltList_stk_self' (compTM A B e) _).symm
    · rw [hA3 q (Nat.zero_le _) hq]
      exact (haltList_stk_ne' (compTM A B e) _ hq).symm
  -- Bounds on the stacks.
  have hT1 : ∑ q, (P1 q).length ≤ LA.length + pushBound A B e * t1 := by
    have h := total_iter A B e t1 (initList (compTM A B e) LA) _ hit1'
    rw [← sum_init_comp A B e LA]
    exact h
  have hLO : LO.length ≤ ∑ q, (P1 q).length := by
    have := Finset.single_le_sum (f := fun q => (P1 q).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Sum.inl A.k₁))
    simp only [hPl] at this
    exact this
  have hpath : (flip bind (TM2.step (Mc A B e)))^[t2 + t1] (some (initList (compTM A B e) LA)) =
      some ⟨liftL (embB A B e) (haltList B LOB).l, (embB A B e).set (haltList B LOB).var (initSc A B),
        P2⟩ := by
    rw [Function.iterate_add_apply, hit1', hit2']
  have hT2 : ∑ q, (P2 q).length ≤ LA.length + pushBound A B e * (t1 + t2) := by
    have h := total_iter A B e (t2 + t1) (initList (compTM A B e) LA) _ hpath
    rw [← sum_init_comp A B e LA, Nat.add_comm t1 t2]
    exact h
  refine ⟨by omega, kc0 + 1, ?_, ?_⟩
  · rw [show t1 + t2 + (kc0 + 1) = (kc0 + 1) + t2 + t1 by omega, Function.iterate_add_apply,
      hit1', Function.iterate_add_apply, hit2', Function.iterate_succ_apply', hit3']
    show TM2.step (Mc A B e) ⟨some (Sum.inr (Sum.inr (Fin.last _))), s3, P3⟩ = _
    rw [hfinal, hP3]
    rfl
  · omega

end Machine

section Final

theorem poly_mono (p : Polynomial ℕ) : ∀ x y : ℕ, x ≤ y → p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on with
  | C a => intro x y _; simp
  | add p q hp hq =>
    intro x y h
    rw [Polynomial.eval_add, Polynomial.eval_add]
    exact Nat.add_le_add (hp x y h) (hq x y h)
  | monomial n a _ =>
    intro x y h
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

/-- The time bound of the composition: `(C + 1)` times the two times, plus the cleanup. -/
noncomputable def timeBound (time1 time2 : Polynomial ℕ) (C N : ℕ) : Polynomial ℕ :=
  Polynomial.C (C + 1) * (time1 + time2.comp (Polynomial.X + Polynomial.C C * time1)) +
    Polynomial.X + Polynomial.C (2 * N + 2)

theorem timeBound_eval (time1 time2 : Polynomial ℕ) (C N n : ℕ) :
    (timeBound time1 time2 C N).eval n =
      (C + 1) * (time1.eval n + time2.eval (n + C * time1.eval n)) + n + (2 * N + 2) := by
  simp [timeBound, Polynomial.eval_comp]

/-- Composition of two polynomial-time machines. -/
noncomputable def compose {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    TM2ComputableInPolyTime eα eγ (g ∘ f) := by
  haveI : Fintype h1.tm.K := h1.tm.kFin
  haveI : Fintype h2.tm.K := h2.tm.kFin
  haveI : Fintype h1.tm.Λ := h1.tm.ΛFin
  haveI : Fintype h2.tm.Λ := h2.tm.ΛFin
  haveI : Fintype h1.tm.σ := h1.tm.σFin
  haveI : Fintype h2.tm.σ := h2.tm.σFin
  haveI : Fintype (h1.tm.Γ h1.tm.k₀) := h1.tm.Γk₀Fin
  refine
    { tm := compTM h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm)
      inputAlphabet := h1.inputAlphabet
      outputAlphabet :=
        (eps h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) h2.tm.k₁).trans
          h2.outputAlphabet
      time := timeBound h1.time h2.time
        (pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm))
        (Fintype.card (h1.tm.K ⊕ h2.tm.K))
      outputsFun := fun a => ?_ }
  have H1 := h1.outputsFun a
  have H2 := h2.outputsFun (f a)
  have hLB : List.map h2.inputAlphabet.invFun (eβ (f a)) =
      (List.map h1.outputAlphabet.invFun (eβ (f a))).map
        (h1.outputAlphabet.trans h2.inputAlphabet.symm) := by
    rw [List.map_map]
    congr 1
    funext y
    simp
  have hcr := comp_run h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm)
    (List.map h1.inputAlphabet.invFun (eα a)) (List.map h1.outputAlphabet.invFun (eβ (f a)))
    H1.steps H1.evals_in_steps (List.map h2.inputAlphabet.invFun (eβ (f a))) hLB H2.steps
    (List.map h2.outputAlphabet.invFun (eγ (g (f a)))) H2.evals_in_steps
  have hlo := hcr.1
  have hspec := Classical.choose_spec hcr.2
  have hout : (List.map h2.outputAlphabet.invFun (eγ (g (f a)))).map
      (eps h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) h2.tm.k₁).symm =
      List.map ((eps h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) h2.tm.k₁).trans
        h2.outputAlphabet).invFun (eγ (g (f a))) := by
    rw [List.map_map]
    rfl
  have hn : (List.map h1.inputAlphabet.invFun (eα a)).length = (eα a).length := by simp
  have hLOlen : (List.map h1.outputAlphabet.invFun (eβ (f a))).length = (eβ (f a)).length := by
    simp
  have hH1 := H1.steps_le_m
  have hH2 := H2.steps_le_m
  have hC : pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) * H1.steps ≤
      pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) *
        h1.time.eval (eα a).length := Nat.mul_le_mul_left _ hH1
  have hLe : (eβ (f a)).length ≤ (eα a).length +
      pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) *
        h1.time.eval (eα a).length := by
    omega
  have hT2 : H2.steps ≤ h2.time.eval ((eα a).length +
      pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) *
        h1.time.eval (eα a).length) :=
    le_trans hH2 (poly_mono h2.time _ _ hLe)
  refine ⟨⟨H1.steps + H2.steps + Classical.choose hcr.2, ?_⟩, ?_⟩
  · exact hspec.1.trans (congrArg (fun L => some (haltList
      (compTM h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm)) L)) hout)
  · have hkc := hspec.2
    rw [timeBound_eval]
    have hmul : (pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) + 1) *
        (H1.steps + H2.steps) ≤
        (pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) + 1) *
          (h1.time.eval (eα a).length + h2.time.eval ((eα a).length +
            pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) *
              h1.time.eval (eα a).length)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : (pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) + 1) *
        (H1.steps + H2.steps) = (H1.steps + H2.steps) +
        pushBound h1.tm h2.tm (h1.outputAlphabet.trans h2.inputAlphabet.symm) *
          (H1.steps + H2.steps) := by
      ring
    have hH1' : H1.steps ≤ h1.time.eval (eα a).length := hH1
    linarith

theorem main : ∀ {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
    {eγ : γ → List γΓ} {f : α → β} {g : β → γ},
    TM2ComputableInPolyTime eα eβ f → TM2ComputableInPolyTime eβ eγ g →
      Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  intro α β γ αΓ βΓ γΓ eα eβ eγ f g h1 h2
  exact ⟨compose h1 h2⟩

end Final

end MPP.Solutions.Pnp006
