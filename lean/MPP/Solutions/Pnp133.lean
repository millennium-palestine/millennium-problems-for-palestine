import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp132

namespace MPP.Solutions.Pnp133

open MPP.PvsNP Computability Turing

theorem main : ∃ L : Lang, InNP L ∧ ∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length ≤ x.length ∧
    (x.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([], w, none)).1.headD false = true := by
  classical
  obtain ⟨V, hV, heq⟩ := MPP.Solutions.Pnp132.main
  refine ⟨fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧ V (pair x w) = true), ?_, ?_⟩
  · unfold InNP
    refine ⟨V, hV, Polynomial.X, fun x => ?_⟩
    simp [Polynomial.eval_X]
  · intro x
    simp only [decide_eq_true_iff, heq]
    -- the two `match` expressions are separate auxiliary matchers, equal by unfolding
    exact Iff.rfl

end MPP.Solutions.Pnp133
