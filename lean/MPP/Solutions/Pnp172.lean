import Mathlib
import MPP.Solutions.Pnp171

namespace MPP.Solutions.Pnp172

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool),
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
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s.take (2 * ps.countP (fun q => q.1 && q.2) + 1), w, none)).1
      ++ s.drop (2 * ps.countP (fun q => q.1 && q.2) + 1) := by
  intro ps s w
  by_cases hk : 2 * ps.countP (fun q => q.1 && q.2) + 1 ≤ s.length
  · have h := MPP.Solutions.Pnp171.main ps (s.take (2 * ps.countP (fun q => q.1 && q.2) + 1))
      (s.drop (2 * ps.countP (fun q => q.1 && q.2) + 1)) w (by simp only [List.length_take]; omega)
    rw [List.take_append_drop] at h
    exact h
  · have ht : s.take (2 * ps.countP (fun q => q.1 && q.2) + 1) = s :=
      List.take_of_length_le (by omega)
    have hd : s.drop (2 * ps.countP (fun q => q.1 && q.2) + 1) = [] :=
      List.drop_of_length_le (by omega)
    rw [ht, hd, List.append_nil]

end MPP.Solutions.Pnp172
