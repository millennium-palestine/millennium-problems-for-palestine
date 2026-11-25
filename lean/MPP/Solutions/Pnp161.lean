import Mathlib

namespace MPP.Solutions.Pnp161

theorem main : ∀ (x : List Bool) (s : List ℕ × ℕ × Option Bool),
    x.foldl (fun (st : List ℕ × ℕ × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD 0 :: st.1, st.2.1, none)
          else (st.2.1 :: st.1, st.2.1 + 1, none))) ([], 1, none) = s →
    s.1.Pairwise (· ≥ ·) ∧ ∀ u ∈ s.1, u < s.2.1 := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool),
      (st.1.Pairwise (· ≥ ·) ∧ (∀ u ∈ st.1, u < st.2.1) ∧ 1 ≤ st.2.1) →
      ∀ s : List ℕ × ℕ × Option Bool,
        x.foldl (fun (st : List ℕ × ℕ × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none)
              else (st.2.1 :: st.1, st.2.1 + 1, none))) st = s →
        (s.1.Pairwise (· ≥ ·) ∧ (∀ u ∈ s.1, u < s.2.1) ∧ 1 ≤ s.2.1) := by
    intro x
    induction x with
    | nil =>
      intro st hst s hs
      subst hs
      exact hst
    | cons b xs ih =>
      intro st hst s hs
      rw [List.foldl_cons] at hs
      refine ih _ ?_ s hs
      rcases st with ⟨stk, t, pend⟩
      obtain ⟨h1, h2, h3⟩ := hst
      dsimp only at h1 h2 h3 ⊢
      cases pend with
      | none => exact ⟨h1, h2, h3⟩
      | some a =>
        cases a <;> cases b <;> try dsimp only
        · -- leaf: push the time, advance it
          refine ⟨List.pairwise_cons.2 ⟨fun y hy => (h2 y hy).le, h1⟩, ?_, Nat.le_succ_of_le h3⟩
          intro u hu
          rcases List.mem_cons.1 hu with rfl | hu
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (h2 u hu)
        · -- copy: push the top entry (0 on an empty stack)
          cases stk with
          | nil =>
            refine ⟨by simp, ?_, h3⟩
            intro u hu
            simp at hu
            subst hu
            exact h3
          | cons x rest =>
            have hx : x < t := h2 x (by simp)
            refine ⟨?_, ?_, h3⟩
            · refine List.pairwise_cons.2 ⟨?_, h1⟩
              intro y hy
              rcases List.mem_cons.1 hy with rfl | hy'
              · exact le_refl _
              · exact (List.pairwise_cons.1 h1).1 y hy'
            · intro u hu
              rcases List.mem_cons.1 hu with h | hu
              · rw [h]
                simpa using hx
              · exact h2 u hu
        · -- (true, false): nothing happens
          exact ⟨h1, h2, h3⟩
        · -- NAND: pop two, push the time, advance it
          refine ⟨List.pairwise_cons.2 ⟨?_, List.Pairwise.sublist (List.drop_sublist 2 stk) h1⟩, ?_, Nat.le_succ_of_le h3⟩
          · intro y hy
            exact (h2 y ((List.drop_sublist 2 stk).subset hy)).le
          · intro u hu
            rcases List.mem_cons.1 hu with rfl | hu
            · exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h2 u ((List.drop_sublist 2 stk).subset hu))
  intro x s h
  have hs := key x ([], 1, none) ⟨List.Pairwise.nil, fun u hu => by simp at hu, le_refl 1⟩ s h
  exact ⟨hs.1, hs.2.1⟩

end MPP.Solutions.Pnp161
