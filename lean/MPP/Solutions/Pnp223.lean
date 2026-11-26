import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp223

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (k : Nat) (s w : List Bool), k ≤ w.length →
      ((List.replicate k [false, false]).flatten).foldl step (s, w, none) = ((w.take k).reverse ++ s, w.drop k, none) := by
  intro step k
  induction k with
  | zero => intro s w _; simp
  | succ k ih =>
    intro s w hk
    cases w with
    | nil => simp at hk
    | cons b w' =>
      have hk' : k ≤ w'.length := by simp at hk; omega
      rw [List.replicate_succ, List.flatten_cons, List.foldl_append]
      have h1 : [false, false].foldl step (s, b :: w', none) = (b :: s, w', none) := rfl
      rw [h1, ih (b :: s) w' hk']
      simp [List.take_succ_cons, List.reverse_cons, List.append_assoc, List.drop_succ_cons]

end MPP.Solutions.Pnp223
