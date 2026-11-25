import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp150

open MPP.PvsNP Computability Turing

theorem main : let step := fun (st : List Bool × List Bool × Option Bool) (c : Bool) =>
    match st.2.2 with
    | none => (st.1, st.2.1, some c)
    | some d =>
      if d then (if c then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
        else (st.1, st.2.1, none))
      else (if c then (st.1.headD false :: st.1, st.2.1, none)
        else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))
  ∀ (k : ℕ) (p : List Bool) (s : List Bool × List Bool × Option Bool),
    (p.foldl step s).2.2 = none →
    (p ++ (List.replicate k [true, false]).flatten).foldl step s = p.foldl step s := by
  intro step k p s hs
  rw [List.foldl_append]
  generalize p.foldl step s = t at hs ⊢
  have key : step (step t true) false = t := by
    obtain ⟨a, w, q⟩ := t
    simp only at hs
    subst hs
    simp [step]
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [key, ih]

end MPP.Solutions.Pnp150
