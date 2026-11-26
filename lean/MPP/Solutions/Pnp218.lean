import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp218

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (a w : List Bool),
      [false, true, true, true].foldl step (a, w, none) = ((!(a.headD false)) :: a.drop 1, w, none) := by
  intro step a w
  rcases a with _ | ⟨h, t⟩
  · rfl
  · cases h <;> rfl

end MPP.Solutions.Pnp218
