import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp232

namespace MPP.Solutions.Pnp241

open MPP.PvsNP Turing

theorem main : ∀ a b s : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) a) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) b) →
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) s) →
    (∀ x w : List Bool, s (pair x w) = pair x (w ++ [(List.range ((pair x (List.replicate w.length false)).length + 1)).any
          (fun m =>
            w.getD (a (pair (pair x (List.replicate w.length false)) (List.replicate m true))).length false &&
              w.getD (b (pair (pair x (List.replicate w.length false)) (List.replicate m true))).length false)])) →
    ∀ p : Polynomial ℕ, ∃ T : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) T) ∧
      ∀ x w : List Bool, T (pair x w) = s^[p.eval (pair x w).length] (pair x w) := by
  intro a b s _ _ hs hcell p
  exact MPP.Solutions.Pnp232.main s hs (fun x w => ⟨_, hcell x w⟩) p

end MPP.Solutions.Pnp241
