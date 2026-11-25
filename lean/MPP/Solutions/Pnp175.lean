import Mathlib

namespace MPP.Solutions.Pnp175

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool),
    ps.countP (fun q => q.1 && q.2) + 1 ≤ s.length →
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1.length
      + ps.countP (fun q => q.1 && q.2)
    = s.length + ps.countP (fun q => !q.1) := by
  intro ps
  induction ps with
  | nil => intro s w _; simp
  | cons q ps ih =>
    intro s w hN
    obtain ⟨a, b⟩ := q
    cases a <;> cases b
    · -- leaf: pushes one cell, the NAND count is unchanged
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons,
        Bool.false_eq_true, ↓reduceIte, List.countP_cons, Bool.and_false, Bool.not_false] at hN ⊢
      have key := ih (w.headD false :: s) (List.drop 1 w) (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at key
      omega
    · -- copy: pushes one cell, the NAND count is unchanged
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons,
        Bool.false_eq_true, ↓reduceIte, List.countP_cons, Bool.false_and, Bool.not_false] at hN ⊢
      have key := ih (s.headD false :: s) w (by simp only [List.length_cons]; omega)
      simp only [List.length_cons] at key
      omega
    · -- no-op: the stack is unchanged
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons,
        Bool.false_eq_true, ↓reduceIte, List.countP_cons, Bool.true_and, Bool.not_true] at hN ⊢
      have key := ih s w (by omega)
      omega
    · -- NAND: pops two cells and pushes one, the NAND count drops by one
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons,
        Bool.false_eq_true, ↓reduceIte, List.countP_cons, Bool.true_and, Bool.not_true] at hN ⊢
      have key := ih ((!(s.headD false && (List.drop 1 s).headD false)) :: List.drop 2 s) w
        (by simp only [List.length_cons, List.length_drop]; omega)
      simp only [List.length_cons, List.length_drop] at key
      omega

end MPP.Solutions.Pnp175
