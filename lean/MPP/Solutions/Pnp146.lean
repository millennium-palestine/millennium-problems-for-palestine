import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp146

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
  ∀ (k : ℕ) (st : List Bool × List Bool × Option Bool), st.2.2 = none →
    (fun s => step (step s true) false)^[k] st = st := by
  intro step k st hst
  have key : step (step st true) false = st := by
    obtain ⟨s, w, p⟩ := st
    simp only at hst
    subst hst
    simp [step]
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    exact key

end MPP.Solutions.Pnp146
