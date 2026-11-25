import Mathlib

namespace MPP.Solutions.Pnp170

/-- The head of a list is determined by its first entry. -/
theorem headD_agree (w w' : List Bool) (h : w.take 1 = w'.take 1) :
    w.headD false = w'.headD false := by
  rcases w with _ | ⟨a, t⟩ <;> rcases w' with _ | ⟨c, u⟩ <;> simp_all

/-- Two lists that agree on their first `N` entries agree on their first `M ≤ N` entries. -/
theorem take_agree {s s' : List Bool} {N M : ℕ} (h : s.take N = s'.take N) (hM : M ≤ N) :
    s.take M = s'.take M := by
  have h' := congrArg (List.take M) h
  simpa only [List.take_take, min_eq_left hM] using h'

/-- Dropping one entry shifts the agreement window by one. -/
theorem drop_one_agree {w w' : List Bool} {m : ℕ} (h : w.take (1 + m) = w'.take (1 + m)) :
    (w.drop 1).take m = (w'.drop 1).take m := by
  rw [List.take_drop, List.take_drop, h]

theorem main : ∀ (ps : List (Bool × Bool)) (s w w' : List Bool),
    w.take (ps.countP fun q => !q.1 && !q.2) = w'.take (ps.countP fun q => !q.1 && !q.2) →
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1
    = ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w', none)).1 := by
  intro ps
  induction ps with
  | nil => intro s w w' _; simp
  | cons p ps ih =>
    intro s w w' h
    obtain ⟨a, b⟩ := p
    cases a <;> cases b
    · -- a leaf: it pushes the first witness bit and drops it
      have hc : ((false, false) :: ps).countP (fun q => !q.1 && !q.2) =
          ps.countP (fun q => !q.1 && !q.2) + 1 := by
        simp
      rw [hc] at h
      have hh : w.headD false = w'.headD false :=
        headD_agree w w' (take_agree h (by omega))
      have ht := drop_one_agree (w := w) (w' := w') (m := ps.countP (fun q => !q.1 && !q.2))
        (by rwa [Nat.add_comm])
      have e1 : [false, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (w.headD false :: s, w.drop 1, none) := rfl
      have e2 : [false, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w', none)
          = (w'.headD false :: s, w'.drop 1, none) := rfl
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2, hh]
      exact ih _ _ _ ht
    · -- copy: the witness is untouched
      have hc : ((false, true) :: ps).countP (fun q => !q.1 && !q.2) =
          ps.countP (fun q => !q.1 && !q.2) := by
        simp
      rw [hc] at h
      have e1 : [false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (s.headD false :: s, w, none) := rfl
      have e2 : [false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w', none)
          = (s.headD false :: s, w', none) := rfl
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ih _ _ _ h
    · -- no-op: the witness is untouched
      have hc : ((true, false) :: ps).countP (fun q => !q.1 && !q.2) =
          ps.countP (fun q => !q.1 && !q.2) := by
        simp
      rw [hc] at h
      have e1 : [true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (s, w, none) := rfl
      have e2 : [true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w', none)
          = (s, w', none) := rfl
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ih _ _ _ h
    · -- NAND: the witness is untouched
      have hc : ((true, true) :: ps).countP (fun q => !q.1 && !q.2) =
          ps.countP (fun q => !q.1 && !q.2) := by
        simp
      rw [hc] at h
      have e1 : [true, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = ((!(s.headD false && (s.drop 1).headD false)) :: s.drop 2, w, none) := rfl
      have e2 : [true, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w', none)
          = ((!(s.headD false && (s.drop 1).headD false)) :: s.drop 2, w', none) := rfl
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ih _ _ _ h

end MPP.Solutions.Pnp170
