import Mathlib

namespace MPP.Solutions.Pnp177

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool),
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).2.2 = none := by
  have key : ∀ (ps : List (Bool × Bool)) (st : List Bool × List Bool × Option Bool), st.2.2 = none →
      ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st).2.2 = none := by
    intro ps
    induction ps with
    | nil => intro st h; simpa using h
    | cons q ps ih =>
      intro st h
      obtain ⟨a, b⟩ := q
      obtain ⟨s, w, p⟩ := st
      dsimp only at h
      subst h
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
      apply ih
      cases a <;> cases b <;> simp
  intro ps s w
  exact key ps (s, w, none) rfl

end MPP.Solutions.Pnp177
