import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp144

open MPP.PvsNP Computability Turing

theorem main : ∀ (a b : Bool) (rest w : List Bool),
    ([true, true, false, true].foldl (fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some c)
      | some d =>
        if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if c then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (a :: b :: rest, w, none)).1
      = (!(a && b)) :: (!(a && b)) :: rest := by
  intro a b rest w
  cases a <;> cases b <;> simp

end MPP.Solutions.Pnp144
