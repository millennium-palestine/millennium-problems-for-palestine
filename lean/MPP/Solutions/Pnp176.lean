import Mathlib

namespace MPP.Solutions.Pnp176

theorem main : ∀ (x : List Bool) (st : List Bool × List Bool × Option Bool),
    (x.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) st).1.length
      ≤ st.1.length + x.length := by
  intro x
  induction x with
  | nil => intro st; simp
  | cons b x ih =>
    intro st
    rw [List.foldl_cons, List.length_cons]
    refine le_trans (ih _) ?_
    rcases st with ⟨s, w, _ | a⟩
    · cases b <;> simp <;> omega
    · cases a <;> cases b <;> simp <;> omega

end MPP.Solutions.Pnp176
