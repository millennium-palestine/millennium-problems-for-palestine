import Mathlib

namespace MPP.Solutions.Pnp174

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool),
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).2.1
    = w.drop (ps.countP fun q => !q.1 && !q.2) := by
  intro ps
  induction ps with
  | nil => intro s w; simp
  | cons q ps ih =>
    intro s w
    obtain ⟨a, b⟩ := q
    cases a <;> cases b <;>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append,
        List.foldl_cons, Bool.false_eq_true, ↓reduceIte] <;>
      rw [ih] <;>
      simp [Nat.add_comm]

end MPP.Solutions.Pnp174
