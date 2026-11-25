import Mathlib

namespace MPP.Solutions.Pnp186

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

theorem main : ∀ (ps : List (Bool × Bool)) (t w : List Bool), t.length ≤
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

end MPP.Solutions.Pnp186
