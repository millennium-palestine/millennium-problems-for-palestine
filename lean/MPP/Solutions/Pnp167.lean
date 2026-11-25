import Mathlib

namespace MPP.Solutions.Pnp167

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
    ∀ t : ℕ, s.2.2.2.countP (fun p => decide (p.2 = t)) ≤ 2 := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      ((∀ p ∈ st.2.2.2, p.2 < st.2.1) ∧
        ∀ t : ℕ, st.2.2.2.countP (fun p => decide (p.2 = t)) ≤ 2) →
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
      ∀ t : ℕ, (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
          match st.2.2.1 with
          | none => (st.1, st.2.1, some b, st.2.2.2)
          | some a =>
            if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
                ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
              else (st.1, st.2.1, none, st.2.2.2))
            else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
              else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.2.2.countP
            (fun p => decide (p.2 = t)) ≤ 2) := by
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
          refine ⟨?_, ?_⟩
          · intro p hp
            exact Nat.lt_succ_of_lt (h1 p hp)
          · exact h2
        · -- push the top entry (0 on an empty stack); the counter and the log are kept
          exact ⟨h1, h2⟩
        · -- no-op on the stack, the counter and the log
          exact ⟨h1, h2⟩
        · -- NAND: the new arcs all carry the old time t, the counter advances to t + 1
          have hnew : ∀ p ∈ ((stk.take 2).filter (· != 0)).map (fun u => (u, t)), p.2 = t := by
            intro p hp
            obtain ⟨u, _, rfl⟩ := List.mem_map.1 hp
            rfl
          have hlen : (((stk.take 2).filter (· != 0)).map (fun u => (u, t))).length ≤ 2 := by
            rw [List.length_map]
            exact le_trans (List.length_filter_le _ _) (by simp)
          refine ⟨?_, ?_⟩
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · rw [hnew p hp]
              exact Nat.lt_succ_self _
            · exact Nat.lt_succ_of_lt (h1 p hp)
          · intro t'
            rw [List.countP_append]
            rcases eq_or_ne t' t with ht | ht
            · have hold : arcs.countP (fun p => decide (p.2 = t')) = 0 := by
                apply List.countP_eq_zero.2
                intro p hp
                have h3 : p.2 < t := h1 p hp
                simp only [decide_eq_true_eq]
                omega
              rw [hold, Nat.add_zero, ht]
              exact le_trans List.countP_le_length hlen
            · have hnw : (((stk.take 2).filter (· != 0)).map (fun u => (u, t))).countP
                  (fun p => decide (p.2 = t')) = 0 := by
                apply List.countP_eq_zero.2
                intro p hp h
                exact ht ((of_decide_eq_true h).symm.trans (hnew p hp))
              rw [hnw, Nat.zero_add]
              exact h2 t'
  intro x s hs t
  subst hs
  exact (key x ([], 1, none, []) ⟨by simp, fun t => by simp⟩).2 t
end MPP.Solutions.Pnp167
