import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp145

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
  ∀ st : List Bool × List Bool × Option Bool, st.2.2 = none → step (step st true) false = st := by
  intro step st hst
  obtain ⟨s, w, p⟩ := st
  simp only at hst
  subst hst
  simp [step]

end MPP.Solutions.Pnp145
