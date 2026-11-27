import Mathlib

namespace MPP.Solutions.Pnp273

-- every bit list is a list of pairs followed by at most one leftover bit
theorem split_bits : ∀ x : List Bool, ∃ (q : List (Bool × Bool)) (o : List Bool),
    x = q.flatMap (fun r : Bool × Bool => [r.1, r.2]) ++ o ∧ o.length ≤ 1
  | [] => ⟨[], [], by simp, by simp⟩
  | [a] => ⟨[], [a], by simp, by simp⟩
  | a :: b :: rest => by
    obtain ⟨q, o, h1, h2⟩ := split_bits rest
    exact ⟨(a, b) :: q, o, by simp [h1], h2⟩

-- a run of pairs from a state with no pending bit ends with no pending bit
theorem pending_none (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hnone : ∀ st b, st.2.2 = none → (F st b).2.2 = some b ∧ (F st b).1 = st.1)
    (hsome : ∀ st a b, st.2.2 = some a → (F st b).2.2 = none) :
    ∀ (q : List (Bool × Bool)) (st : List Bool × List Bool × Option Bool), st.2.2 = none →
      (List.foldl F st (q.flatMap fun r : Bool × Bool => [r.1, r.2])).2.2 = none
  | [], st, h => by simpa using h
  | r :: q, st, h => by
    simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact pending_none F hnone hsome q _ (hsome _ _ _ (hnone st r.1 h).1)

-- a leftover bit read from a state with no pending bit leaves the top unchanged
theorem leftover_keeps_top (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hnone : ∀ st b, st.2.2 = none → (F st b).2.2 = some b ∧ (F st b).1 = st.1)
    (hsome : ∀ st a b, st.2.2 = some a → (F st b).2.2 = none)
    (s0 : List Bool × List Bool × Option Bool) (hs0 : s0.2.2 = none)
    (q : List (Bool × Bool)) (o : List Bool) (ho : o.length ≤ 1) :
    (List.foldl F s0 (q.flatMap (fun r : Bool × Bool => [r.1, r.2]) ++ o)).1 =
      (List.foldl F s0 (q.flatMap (fun r : Bool × Bool => [r.1, r.2]))).1 := by
  have hp := pending_none F hnone hsome q s0 hs0
  rcases o with _ | ⟨c, _ | ⟨d, l⟩⟩
  · simp
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (hnone _ c hp).2
  · simp only [List.length_cons] at ho
    omega

theorem main : ∀ (x : List Bool) (v : Bool) (t w : List Bool), ∃ q : List (Bool × Bool),
    (x.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)).1.headD false =
    ((q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)).1.headD false := by
  intro x v t w
  obtain ⟨q, o, rfl, ho⟩ := split_bits x
  refine ⟨q, ?_⟩
  exact congrArg (fun s : List Bool => s.headD false)
    (leftover_keeps_top _ (by intro st b h; simp [h]) (by intro st a b h; simp only [h]; split_ifs <;> rfl)
      (v :: t, w, none) rfl q o ho)

end MPP.Solutions.Pnp273
