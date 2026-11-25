import Mathlib

namespace MPP.Solutions.Pnp155

/-- A leaf pair `[false, false]` pushes the first witness bit and drops it. -/
theorem leaf_step (s w : List Bool) :
    ([false, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
      = (w.headD false :: s, w.drop 1, none) := rfl

/-- A copy pair `[false, true]` pushes a copy of the top of the stack. -/
theorem copy_step (s w : List Bool) :
    ([false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
      = (s.headD false :: s, w, none) := rfl

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool), (∀ q ∈ ps, q.1 = false) → ∃ (t : List Bool),
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1
      = t ++ s ∧ t.length = ps.length
      ∧ ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).2.1
        = w.drop (ps.filter (fun q => !q.2)).length := by
  intro ps
  induction ps with
  | nil => intro s w _; exact ⟨[], by simp⟩
  | cons p ps ih =>
    intro s w hp
    have hps : ∀ q ∈ ps, q.1 = false := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    rcases p with ⟨p1, p2⟩
    have hp0 : p1 = false := hp (p1, p2) (List.mem_cons_self)
    subst hp0
    cases p2
    · obtain ⟨t', h1, h2, h3⟩ := ih (w.headD false :: s) (w.drop 1) hps
      refine ⟨t' ++ [w.headD false], ?_, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.foldl_append]
        rw [leaf_step, h1]
        simp [List.append_assoc]
      · simp [h2]
      · simp only [List.flatMap_cons, List.foldl_append]
        rw [leaf_step, h3]
        simp [List.filter_cons, List.drop_drop, Nat.add_comm]
    · obtain ⟨t', h1, h2, h3⟩ := ih (s.headD false :: s) w hps
      refine ⟨t' ++ [s.headD false], ?_, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.foldl_append]
        rw [copy_step, h1]
        simp [List.append_assoc]
      · simp [h2]
      · simp only [List.flatMap_cons, List.foldl_append]
        rw [copy_step, h3]
        simp [List.filter_cons]

end MPP.Solutions.Pnp155
