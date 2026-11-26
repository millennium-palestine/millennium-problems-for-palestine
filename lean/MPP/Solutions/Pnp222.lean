import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp222

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (x b : Bool) (t w : List Bool),
      [false, false, true, true, false, true, true, true].foldl step ((x :: t), (b :: w), none) =
        (((b && x) :: t), w, none) := by
  intro step x b t w
  cases x <;> cases b <;> rfl

end MPP.Solutions.Pnp222
