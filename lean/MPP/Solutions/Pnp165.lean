import Mathlib

namespace MPP.Solutions.Pnp165

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
    ∀ p ∈ s.2.2.2, p.1 < p.2 ∧ p.2 < s.2.1 := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      ((∀ w ∈ st.1, w < st.2.1) ∧ 1 ≤ st.2.1 ∧ (∀ p ∈ st.2.2.2, p.1 < p.2 ∧ p.2 < st.2.1)) →
      ∀ s : List ℕ × ℕ × Option Bool × List (ℕ × ℕ),
        x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st = s →
        ((∀ w ∈ s.1, w < s.2.1) ∧ 1 ≤ s.2.1 ∧ (∀ p ∈ s.2.2.2, p.1 < p.2 ∧ p.2 < s.2.1)) := by
    intro x
    induction x with
    | nil =>
      intro st h s hs
      subst hs
      exact h
    | cons b xs ih =>
      intro st h s hs
      rw [List.foldl_cons] at hs
      refine ih _ ?_ s hs
      rcases st with ⟨stk, t, pend, arcs⟩
      obtain ⟨h1, h2, h3⟩ := h
      cases pend with
      | none => exact ⟨h1, h2, h3⟩
      | some a =>
        cases a <;> cases b
        · -- push the old time and advance the counter; arcs unchanged
          refine ⟨?_, Nat.le_succ_of_le h2, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h1 w hw)
          · intro p hp
            exact ⟨(h3 p hp).1, Nat.lt_succ_of_lt (h3 p hp).2⟩
        · -- copy: push the top entry (0 on an empty stack); arcs unchanged
          refine ⟨?_, h2, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · cases stk with
              | nil => exact h2
              | cons y ys => exact h1 y (by simp)
            · exact h1 w hw
          · intro p hp
            exact h3 p hp
        · -- no-op on the stack, the counter and the arcs
          exact ⟨h1, h2, h3⟩
        · -- drop two entries, push the old time, advance the counter, record arcs
          refine ⟨?_, Nat.le_succ_of_le h2, ?_⟩
          · intro w hw
            rcases List.mem_cons.1 hw with rfl | hw
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h1 w (List.drop_subset _ _ hw))
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hp
              have hu' : u ∈ stk := List.mem_of_mem_take (List.mem_of_mem_filter hu)
              exact ⟨h1 u hu', Nat.lt_succ_self _⟩
            · exact ⟨(h3 p hp).1, Nat.lt_succ_of_lt (h3 p hp).2⟩
  intro x s hs p hp
  exact (key x ([], 1, none, []) ⟨by simp, le_rfl, by simp⟩ s hs).2.2 p hp

end MPP.Solutions.Pnp165
