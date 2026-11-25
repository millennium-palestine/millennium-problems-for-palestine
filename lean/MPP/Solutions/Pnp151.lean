import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp151

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (k : ℕ) (stk w : List Bool), k ≤ w.length →
      ((List.replicate k [false, false]).flatten).foldl step (stk, w, none)
        = ((w.take k).reverse ++ stk, w.drop k, none) := by
  intro step k
  induction k with
  | zero =>
    intro stk w _
    simp
  | succ k ih =>
    intro stk w hk
    cases w with
    | nil => simp at hk
    | cons b rest =>
      simp only [List.length_cons] at hk
      have hrest : k ≤ rest.length := by omega
      have hpair : [false, false].foldl step (stk, b :: rest, none) = (b :: stk, rest, none) := by
        rfl
      rw [List.replicate_succ, List.flatten_cons, List.foldl_append, hpair]
      rw [ih (b :: stk) rest hrest]
      simp [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons]

end MPP.Solutions.Pnp151
