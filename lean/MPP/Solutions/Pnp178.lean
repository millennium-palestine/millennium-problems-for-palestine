import Mathlib

namespace MPP.Solutions.Pnp178

def stepF (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) :
    List ℕ × ℕ × Option Bool × List (ℕ × ℕ) :=
  match st.2.2.1 with
  | none => (st.1, st.2.1, some b, st.2.2.2)
  | some a =>
    if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
        ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
      else (st.1, st.2.1, none, st.2.2.2))
    else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
      else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))

def Inv (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ st.1, e < st.2.1) ∧ st.1.Pairwise (fun a c => a ≥ c) ∧ 1 ≤ st.2.1 ∧
    (∀ v, 1 ≤ v → v < st.2.1 → v ∈ st.1 ∨ ∃ q ∈ st.2.2.2, q.1 = v) ∧
    (∀ q ∈ st.2.2.2, q.2 < st.2.1) ∧
    (∀ p ∈ st.2.2.2, ∀ v, p.1 < v → v < p.2 → ∃ q ∈ st.2.2.2, q.1 = v ∧ q.2 ≤ p.2)

theorem take_drop_order (S : List ℕ) (hS : S.Pairwise (fun a c => a ≥ c)) :
    ∀ u ∈ S.take 2, ∀ v ∈ S.drop 2, v ≤ u := by
  match S, hS with
  | [], _ => simp
  | [_], _ => simp
  | x :: y :: rest, hS =>
    intro u hu v hv
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hS
    obtain ⟨h3, -⟩ := List.pairwise_cons.mp h2
    simp only [List.take, List.drop, List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl
    · exact h1 v (List.mem_cons_of_mem _ hv)
    · exact h3 v hv

theorem headD_ge (S : List ℕ) (hS : S.Pairwise (fun a c => a ≥ c)) :
    ∀ e ∈ S, S.headD 0 ≥ e := by
  intro e he
  cases S with
  | nil => simp at he
  | cons x t =>
    rcases List.mem_cons.mp he with rfl | he'
    · simp
    · exact (List.pairwise_cons.mp hS).1 e he'

theorem stepF_inv (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) (h : Inv st) :
    Inv (stepF st b) := by
  unfold Inv at h ⊢
  obtain ⟨S, T, p, L⟩ := st
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 ⊢
  cases p with
  | none =>
    simp only [stepF]
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  | some a =>
    cases a <;> cases b
    · -- leaf: push the time, advance it
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, by omega, ?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · omega
        · have := h1 e he'; omega
      · refine List.pairwise_cons.mpr ⟨fun e he => ?_, h2⟩
        have := h1 e he
        show T ≥ e
        omega
      · intro v hv1 hv2
        rcases Nat.lt_or_ge v T with hvT | hvT
        · rcases h4 v hv1 hvT with hm | ⟨q, hq, hq1⟩
          · exact Or.inl (List.mem_cons_of_mem _ hm)
          · exact Or.inr ⟨q, hq, hq1⟩
        · have hvT' : v = T := by omega
          exact Or.inl (by simp [hvT'])
      · intro q hq
        have := h5 q hq
        omega
      · intro p hp v hv1 hv2
        obtain ⟨q, hq, hq1, hq2⟩ := h6 p hp v hv1 hv2
        exact ⟨q, hq, hq1, hq2⟩
    · -- copy: push the top again (0 on an empty stack)
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      have hdge := headD_ge S h2
      have hdlt : S.headD 0 < T := by
        cases S with
        | nil => simp; omega
        | cons x t =>
          have := h1 x (by simp)
          simpa using this
      refine ⟨?_, ?_, h3, ?_, h5, h6⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact hdlt
        · exact h1 e he'
      · refine List.pairwise_cons.mpr ⟨fun e he => ?_, h2⟩
        exact hdge e he
      · intro v hv1 hv2
        rcases h4 v hv1 hv2 with hm | ⟨q, hq, hq1⟩
        · exact Or.inl (List.mem_cons_of_mem _ hm)
        · exact Or.inr ⟨q, hq, hq1⟩
    · -- no-op
      simp only [stepF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    · -- NAND: pop two, push the time, log the popped nonzero ids at the time
      simp only [stepF, ↓reduceIte]
      have hord := take_drop_order S h2
      refine ⟨?_, ?_, by omega, ?_, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · omega
        · have := h1 e ((List.drop_sublist 2 S).subset he')
          omega
      · refine List.pairwise_cons.mpr ⟨fun e he => ?_,
          List.Pairwise.sublist (List.drop_sublist 2 S) h2⟩
        have := h1 e ((List.drop_sublist 2 S).subset he)
        show T ≥ e
        omega
      · intro v hv1 hv2
        rcases Nat.lt_or_ge v T with hvT | hvT
        · rcases h4 v hv1 hvT with hm | ⟨q, hq, hq1⟩
          · have hsplit : v ∈ S.take 2 ∨ v ∈ S.drop 2 :=
              List.mem_append.mp (by rw [List.take_append_drop]; exact hm)
            rcases hsplit with ht | hd
            · refine Or.inr ⟨(v, T), List.mem_append_left _ ?_, rfl⟩
              exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨ht, by simp; omega⟩, rfl⟩
            · exact Or.inl (List.mem_cons_of_mem _ hd)
          · exact Or.inr ⟨q, List.mem_append_right _ hq, hq1⟩
        · have hvT' : v = T := by omega
          exact Or.inl (by simp [hvT'])
      · intro q hq
        rcases List.mem_append.mp hq with hm | hq'
        · obtain ⟨u, _, hpu⟩ := List.mem_map.mp hm
          subst hpu
          show T < T + 1
          omega
        · have := h5 q hq'
          omega
      · intro p hp v hv1 hv2
        rcases List.mem_append.mp hp with hm | hp'
        · obtain ⟨u, hu, hpu⟩ := List.mem_map.mp hm
          obtain ⟨hut, hu0⟩ := List.mem_filter.mp hu
          have hu0' : u ≠ 0 := by simpa using hu0
          subst hpu
          have hu1 : u < v := hv1
          have hvT : v < T := hv2
          rcases h4 v (by omega) hvT with hm' | ⟨q, hq, hq1⟩
          · have hsplit : v ∈ S.take 2 ∨ v ∈ S.drop 2 :=
              List.mem_append.mp (by rw [List.take_append_drop]; exact hm')
            rcases hsplit with ht | hd
            · refine ⟨(v, T), List.mem_append_left _ ?_, rfl, ?_⟩
              · exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨ht, by simp; omega⟩, rfl⟩
              · show T ≤ T
                exact le_refl _
            · have := hord u hut v hd
              omega
          · exact ⟨q, List.mem_append_right _ hq, hq1, by have := h5 q hq; show q.2 ≤ T; omega⟩
        · obtain ⟨q, hq, hq1, hq2⟩ := h6 p hp' v hv1 hv2
          exact ⟨q, List.mem_append_right _ hq, hq1, hq2⟩

theorem init_inv : Inv ([], 1, none, []) := by
  unfold Inv
  refine ⟨by simp, by simp, le_refl _, ?_, by simp, by simp⟩
  intro v hv1 hv2
  exfalso
  simp only at hv2
  omega

theorem main : ∀ (x : List Bool) (s : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
    x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
      match st.2.2.1 with
      | none => (st.1, st.2.1, some b, st.2.2.2)
      | some a =>
        if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
            ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
          else (st.1, st.2.1, none, st.2.2.2))
        else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
          else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) ([], 1, none, []) = s →
    ∀ p ∈ s.2.2.2, ∀ v : ℕ, p.1 < v → v < p.2 → ∃ q ∈ s.2.2.2, q.1 = v ∧ q.2 ≤ p.2 := by
  intro x s hs
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      Inv st → Inv (x.foldl stepF st) := by
    intro x
    induction x with
    | nil => intro st h; exact h
    | cons b x ih => intro st h; exact ih _ (stepF_inv st b h)
  have hI := key x _ init_inv
  rw [← hs]
  unfold Inv at hI
  exact hI.2.2.2.2.2

end MPP.Solutions.Pnp178
