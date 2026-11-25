import Mathlib

namespace MPP.Solutions.Pnp168

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
    s.2.2.2.Pairwise (fun p q => q.2 ≤ p.2) := by
  -- a list of arcs that all carry the same consumer time is sorted in the required order
  have hconst : ∀ (l : List ℕ) (t : ℕ),
      (l.map (fun u => (u, t))).Pairwise (fun p q => q.2 ≤ p.2) := by
    intro l t
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.pairwise_cons]
      exact ⟨fun b hb => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.1 hb
        exact le_refl t, ih⟩
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      ((∀ p ∈ st.2.2.2, p.2 < st.2.1) ∧ st.2.2.2.Pairwise (fun p q => q.2 ≤ p.2)) →
      ((∀ p ∈ (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.2.2,
          p.2 < (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
            match st.2.2.1 with
            | none => (st.1, st.2.1, some b, st.2.2.2)
            | some a =>
              if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                  ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
                else (st.1, st.2.1, none, st.2.2.2))
              else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
                else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.1) ∧
      (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.2.2.Pairwise
            (fun p q => q.2 ≤ p.2)) := by
    intro x
    induction x with
    | nil =>
      intro st h
      exact h
    | cons b xs ih =>
      intro st h
      rw [List.foldl_cons]
      apply ih
      rcases st with ⟨stk, t, pend, arcs⟩
      obtain ⟨h1, h2⟩ := h
      cases pend with
      | none => exact ⟨h1, h2⟩
      | some a =>
        cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · -- push the old time and advance the counter; the log is kept
          exact ⟨fun p hp => Nat.lt_succ_of_lt (h1 p hp), h2⟩
        · -- push the top entry (0 on an empty stack); the counter and the log are kept
          exact ⟨h1, h2⟩
        · -- no-op on the stack, the counter and the log
          exact ⟨h1, h2⟩
        · -- NAND: the new arcs all carry the old time t, the counter advances to t + 1
          refine ⟨?_, ?_⟩
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
              exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h1 p hp)
          · apply List.pairwise_append.2
            refine ⟨hconst _ t, h2, ?_⟩
            intro p hp q hq
            obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
            exact le_of_lt (h1 q hq)
  intro x s hs
  subst hs
  exact (key x ([], 1, none, []) ⟨by simp, by simp⟩).2
end MPP.Solutions.Pnp168
