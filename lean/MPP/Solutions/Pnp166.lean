import Mathlib

namespace MPP.Solutions.Pnp166

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
    ∀ u ∈ s.1, u < s.2.1 := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      ((∀ w ∈ st.1, w < st.2.1) ∧ 1 ≤ st.2.1) →
      ((∀ w ∈ (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).1,
          w < (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.1) ∧
      1 ≤ (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.1) := by
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
        cases a <;> cases b
        · -- push the old time and advance the counter; the stack is otherwise kept
          refine ⟨?_, Nat.le_succ_of_le h2⟩
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (h1 w hw)
        · -- push the top entry (0 on an empty stack); the counter is kept
          refine ⟨?_, h2⟩
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · cases stk with
            | nil => exact h2
            | cons y ys => exact h1 y (by simp)
          · exact h1 w hw
        · -- no-op on the stack and the counter
          exact ⟨h1, h2⟩
        · -- drop two entries, push the old time, advance the counter
          refine ⟨?_, Nat.le_succ_of_le h2⟩
          intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (h1 w (List.drop_subset _ _ hw))
  intro x s hs u hu
  subst hs
  exact (key x ([], 1, none, []) ⟨by simp, le_rfl⟩).1 u hu

end MPP.Solutions.Pnp166
