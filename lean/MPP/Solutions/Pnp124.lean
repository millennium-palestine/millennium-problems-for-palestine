import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp123

namespace MPP.Solutions.Pnp124

open MPP.PvsNP Computability Turing

/-- The satisfiability language of postfix programs with witness leaves. It is in NP with the
verifier of pnp-123 and the polynomial `X`, since the witness is at most as long as the program. -/
theorem main : ∃ L : Lang, InNP L ∧ ∀ x : List Bool, L x = true ↔ ∃ w : List Bool, w.length ≤ x.length ∧
    (x.foldl (fun (st : List Bool × List Bool) (b : Bool) =>
      if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2)
      else (st.2.headD false :: st.1, st.2.drop 1)) ([], w)).1.headD false = true := by
  obtain ⟨V, hV, hVeq⟩ := MPP.Solutions.Pnp123.main
  classical
  refine ⟨fun x => decide (∃ w : List Bool, w.length ≤ x.length ∧
    (x.foldl (fun (st : List Bool × List Bool) (b : Bool) =>
      if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2)
      else (st.2.headD false :: st.1, st.2.drop 1)) ([], w)).1.headD false = true),
    ⟨V, hV, Polynomial.X, fun x => ?_⟩, fun x => decide_eq_true_iff⟩
  simp only [decide_eq_true_iff, Polynomial.eval_X, hVeq]

end MPP.Solutions.Pnp124
