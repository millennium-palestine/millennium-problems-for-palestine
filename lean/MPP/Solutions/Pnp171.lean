import Mathlib

namespace MPP.Solutions.Pnp171

theorem main : ∀ (ps : List (Bool × Bool)) (s r w : List Bool),
    2 * ps.countP (fun q => q.1 && q.2) + 1 ≤ s.length →
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s ++ r, w, none)).1
    = ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1 ++ r := by
  intro ps
  induction ps with
  | nil => intro s r w _; simp
  | cons p ps ih =>
    intro s r w h
    obtain ⟨a, b⟩ := p
    cases a <;> cases b
    · -- leaf: pushes the first witness bit and drops it; the stack below is s ++ r
      have hN : ((false, false) :: ps).countP (fun q => q.1 && q.2) =
          ps.countP (fun q => q.1 && q.2) := by
        simp
      rw [hN] at h
      have e1 : [false, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s ++ r, w, none)
          = (w.headD false :: (s ++ r), w.drop 1, none) := rfl
      have e2 : [false, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (w.headD false :: s, w.drop 1, none) := rfl
      have hc : 2 * ps.countP (fun q => q.1 && q.2) + 1 ≤ (w.headD false :: s).length := by
        simp only [List.length_cons]; omega
      have ht := ih (w.headD false :: s) r (w.drop 1) hc
      rw [List.cons_append] at ht
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ht
    · -- copy: reads the top of s, which exists because the bound forces s ≠ []
      have hN : ((false, true) :: ps).countP (fun q => q.1 && q.2) =
          ps.countP (fun q => q.1 && q.2) := by
        simp
      rw [hN] at h
      have hh : (s ++ r).headD false = s.headD false := by
        rcases s with _ | ⟨x, t⟩
        · simp only [List.length_nil] at h; omega
        · rfl
      have e1 : [false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s ++ r, w, none)
          = ((s ++ r).headD false :: (s ++ r), w, none) := rfl
      have e2 : [false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (s.headD false :: s, w, none) := rfl
      have hc : 2 * ps.countP (fun q => q.1 && q.2) + 1 ≤ (s.headD false :: s).length := by
        simp only [List.length_cons]; omega
      have ht := ih (s.headD false :: s) r w hc
      rw [List.cons_append] at ht
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2, hh]
      exact ht
    · -- no-op: the stack is unchanged
      have hN : ((true, false) :: ps).countP (fun q => q.1 && q.2) =
          ps.countP (fun q => q.1 && q.2) := by
        simp
      rw [hN] at h
      have e1 : [true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s ++ r, w, none)
          = (s ++ r, w, none) := rfl
      have e2 : [true, false].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)
          = (s, w, none) := rfl
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ih s r w h
    · -- NAND: pops the top two cells of s, both present since the bound gives 3 ≤ |s|
      have hN : ((true, true) :: ps).countP (fun q => q.1 && q.2) =
          ps.countP (fun q => q.1 && q.2) + 1 := by
        simp
      rw [hN] at h
      obtain ⟨x, y, t, rfl⟩ : ∃ x y t, s = x :: y :: t := by
        rcases s with _ | ⟨x, _ | ⟨y, t⟩⟩
        · simp only [List.length_nil] at h; omega
        · simp only [List.length_cons, List.length_nil] at h; omega
        · exact ⟨x, y, t, rfl⟩
      have e1 : [true, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ((x :: y :: t) ++ r, w, none)
          = ((!(x && y)) :: (t ++ r), w, none) := rfl
      have e2 : [true, true].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
          match st.2.2 with
          | none => (st.1, st.2.1, some b)
          | some a =>
            if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
              else (st.1, st.2.1, none))
            else (if b then (st.1.headD false :: st.1, st.2.1, none)
              else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (x :: y :: t, w, none)
          = ((!(x && y)) :: t, w, none) := rfl
      have hc : 2 * ps.countP (fun q => q.1 && q.2) + 1 ≤ ((!(x && y)) :: t).length := by
        simp only [List.length_cons] at h ⊢; omega
      have ht := ih ((!(x && y)) :: t) r w hc
      rw [List.cons_append] at ht
      simp only [List.flatMap_cons, List.foldl_append]
      rw [e1, e2]
      exact ht

end MPP.Solutions.Pnp171
