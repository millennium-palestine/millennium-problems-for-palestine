import Mathlib

namespace MPP.Solutions.Pnp188


theorem step_bottom : ∀ (q : Bool × Bool) (t s w : List Bool), 2 ≤ t.length →
    ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t ++ s, w, none))
    = (([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1 ++ s,
       ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).2.1, none)
    ∧ ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).2.2 = none
    ∧ t.length ≤ ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1.length + 1 := by
  intro q t s w ht
  obtain ⟨a, b⟩ := q
  rcases t with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp at ht
  cases a <;> cases b <;> simp [List.foldl]

theorem one_nand : ∀ (q : Bool × Bool) (t w : List Bool), (q.1 && q.2) = true →
    t.length ≤ ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1.length + 1 := by
  intro q t w h
  obtain ⟨a, b⟩ := q
  simp at h
  obtain ⟨rfl, rfl⟩ := h
  simp [List.foldl]
  omega

theorem one_other : ∀ (q : Bool × Bool) (t w : List Bool), (q.1 && q.2) = false →
    t.length ≤ ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1.length := by
  intro q t w h
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp_all [List.foldl]

theorem pend : ∀ (q : Bool × Bool) (t w : List Bool),
    ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).2.2 = none := by
  intro q t w
  obtain ⟨a, b⟩ := q
  cases a <;> cases b <;> simp [List.foldl]

theorem len_main : ∀ (ps : List (Bool × Bool)) (t w : List Bool), t.length ≤
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1.length
      + (ps.filter fun q => q.1 && q.2).length := by
  intro ps
  induction ps with
  | nil => intro t w; simp
  | cons q ps ih =>
    intro t w
    have hP := pend q t w
    have hN := one_nand q t w
    have hO := one_other q t w
    simp only [List.flatMap_cons, List.foldl_append, List.filter_cons]
    generalize hR : ([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)) = R at hP hN hO ⊢
    obtain ⟨T, W, P⟩ := R
    simp only at hP hN hO ⊢
    subst hP
    have hIH := ih T W
    by_cases hq : (q.1 && q.2) = true
    · have := hN hq
      simp only [hq, if_true, List.length_cons]
      omega
    · have hq' : (q.1 && q.2) = false := by simpa using hq
      have := hO hq'
      simp only [hq', Bool.false_eq_true, if_false]
      omega

theorem bottom_main : ∀ (ps : List (Bool × Bool)) (t s w : List Bool),
    (ps.filter fun q => q.1 && q.2).length + 2 ≤ t.length →
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t ++ s, w, none))
    = (((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).1 ++ s,
       ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)).2.1, none) := by
  intro ps
  induction ps with
  | nil => intro t s w _; simp
  | cons q ps ih =>
    intro t s w h
    by_cases hq : (q.1 && q.2) = true
    · simp [hq] at h
      obtain ⟨hE, hZ, hLen⟩ := step_bottom q t s w (by omega)
      simp only [List.flatMap_cons, List.foldl_append]
      rw [hE]
      generalize hR : (([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none))) = R at hZ hLen ⊢
      obtain ⟨X, Y, Z⟩ := R
      simp only at hZ hLen ⊢
      subst hZ
      exact ih X s Y (by omega)
    · have hq' : (q.1 && q.2) = false := by simpa using hq
      simp [hq'] at h
      obtain ⟨hE, hZ, hLen⟩ := step_bottom q t s w (by omega)
      have hO := one_other q t w hq'
      simp only [List.flatMap_cons, List.foldl_append]
      rw [hE]
      generalize hR : (([q.1, q.2].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none))) = R at hZ hLen hO ⊢
      obtain ⟨X, Y, Z⟩ := R
      simp only at hZ hLen hO ⊢
      subst hZ
      exact ih X s Y (by omega)

theorem main : ∀ (ps1 ps2 : List (Bool × Bool)) (t s w : List Bool) (R : List Bool × List Bool × Option Bool),
  R = ((ps1.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t, w, none)) →
  (ps1.filter fun q => q.1 && q.2).length + (ps2.filter fun q => q.1 && q.2).length + 2 ≤ t.length →
  (((ps1 ++ ps2).flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (t ++ s, w, none)).1 =
    ((ps2.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (R.1, R.2.1, none)).1 ++ s := by
  intro ps1 ps2 t s w R hR h
  subst hR
  have hA := len_main ps1 t w
  have hB := bottom_main ps1 t s w (by omega)
  rw [List.flatMap_append, List.foldl_append, hB]
  rw [bottom_main ps2 _ s _ (by omega)]

end MPP.Solutions.Pnp188
