import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp215

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
    ∀ (p : List Bool) (k : Nat) (s : List Bool × List Bool × Option Bool),
      (p.foldl step s).2.2 = none →
        (p ++ (List.replicate k [true, false]).flatten).foldl step s = p.foldl step s := by
  intro step p k s h
  have pair : ∀ t : List Bool × List Bool × Option Bool, t.2.2 = none →
      [true, false].foldl step t = t := by
    rintro ⟨a, b, _ | d⟩ h
    · rfl
    · simp at h
  rw [List.foldl_append]
  generalize p.foldl step s = t at h ⊢
  induction k generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, pair t h]
    exact ih t h

end MPP.Solutions.Pnp215
