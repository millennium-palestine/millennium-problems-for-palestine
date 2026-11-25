import Mathlib

namespace MPP.Solutions.Pnp164

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
    s.2.2.2.length ≤ x.length := by
  have key : ∀ (x : List Bool) (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)),
      (x.foldl (fun (st : List ℕ × ℕ × Option Bool × List (ℕ × ℕ)) (b : Bool) =>
        match st.2.2.1 with
        | none => (st.1, st.2.1, some b, st.2.2.2)
        | some a =>
          if a then (if b then (st.2.1 :: st.1.drop 2, st.2.1 + 1, none,
              ((st.1.take 2).filter (· != 0)).map (fun u => (u, st.2.1)) ++ st.2.2.2)
            else (st.1, st.2.1, none, st.2.2.2))
          else (if b then (st.1.headD 0 :: st.1, st.2.1, none, st.2.2.2)
            else (st.2.1 :: st.1, st.2.1 + 1, none, st.2.2.2))) st).2.2.2.length
        ≤ st.2.2.2.length + x.length + (if st.2.2.1.isSome then 1 else 0) := by
    intro x
    induction x with
    | nil =>
      intro st
      simp
    | cons b xs ih =>
      intro st
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      rcases st with ⟨stk, t, pend, arcs⟩
      have htake : ((stk.take 2).filter (· != 0)).length ≤ 2 :=
        (List.length_filter_le _ _).trans (List.length_take.trans_le (min_le_left _ _))
      cases pend with
      | none =>
        cases b <;> simp
      | some a =>
        cases a <;> cases b <;> simp <;> omega
  intro x s hs
  subst hs
  simpa using key x ([], 1, none, [])

end MPP.Solutions.Pnp164
