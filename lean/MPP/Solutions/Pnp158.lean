import Mathlib

namespace MPP.Solutions.Pnp158

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

/-- A NAND pair `[true, true]` pops two and pushes their negated conjunction. -/
theorem nand_step (s w : List Bool) :
    ([true, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
      = ((!(s.headD false && (s.drop 1).headD false)) :: s.drop 2, w, none) := rfl

/-- A no-op pair `[true, false]` leaves the stack and the witness alone. -/
theorem noop_step (s w : List Bool) :
    ([true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
      = (s, w, none) := rfl

theorem main : ∀ (ps : List (Bool × Bool)) (s s' w w' : List Bool), s.length = s'.length →
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1.length
      = ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s', w', none)).1.length := by
  intro ps
  induction ps with
  | nil => intro s s' w w' hs; simp [hs]
  | cons p ps ih =>
    intro s s' w w' hs
    rcases p with ⟨p1, p2⟩
    simp only [List.flatMap_cons, List.foldl_append]
    cases p1 <;> cases p2
    · rw [leaf_step, leaf_step]
      exact ih _ _ _ _ (by simp [hs])
    · rw [copy_step, copy_step]
      exact ih _ _ _ _ (by simp [hs])
    · rw [noop_step, noop_step]
      exact ih _ _ _ _ hs
    · rw [nand_step, nand_step]
      exact ih _ _ _ _ (by simp [hs])

end MPP.Solutions.Pnp158
