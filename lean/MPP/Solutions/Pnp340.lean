import Mathlib
import MPP.Solutions.Pnp212

namespace MPP.Solutions.Pnp340

theorem main : ∀ x w : List Bool, (x.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some b)
    | some a =>
      if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if b then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([], w, none)) =
  x.foldl MPP.Solutions.Pnp212.step212 ([], w, none) := by
  intro x w
  rfl

end MPP.Solutions.Pnp340
