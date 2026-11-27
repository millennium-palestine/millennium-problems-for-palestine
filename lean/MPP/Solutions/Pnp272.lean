import Mathlib

namespace MPP.Solutions.Pnp272

theorem main : ∀ (q : List (Bool × Bool)) (c v : Bool) (t w : List Bool),
    (((q.flatMap fun r : Bool × Bool => [r.1, r.2]) ++ [c]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
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
  intro q c v t w
  have key : ∀ (L : List (Bool × Bool)) (s : List Bool × List Bool × Option Bool), s.2.2 = none →
      ((L.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) s).2.2 = none := by
    intro L
    induction L with
    | nil => intro s hs; simpa using hs
    | cons p L ih =>
      intro s hs
      obtain ⟨a, b⟩ := p
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
      apply ih
      cases a <;> cases b <;> simp [hs]
  have final : ∀ (st : List Bool × List Bool × Option Bool), st.2.2 = none →
      ([c].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st).1.headD false = st.1.headD false := by
    intro st h
    rw [List.foldl_cons, List.foldl_nil]
    simp [h]
  rw [List.foldl_append]
  exact final _ (key q (v :: t, w, none) rfl)

end MPP.Solutions.Pnp272
