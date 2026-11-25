import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp147

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (p q : List Bool) (s : List Bool × List Bool × Option Bool),
      (p ++ q).foldl step s = q.foldl step (p.foldl step s) := by
  intro step p q s
  simp only [List.foldl_append]

end MPP.Solutions.Pnp147
