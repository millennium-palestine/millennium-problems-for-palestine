import Mathlib

namespace MPP.Solutions.Pnp139

theorem main : ∀ (g : List Bool → Bool) (x c : List Bool) (k : ℕ),
    (List.range k).foldl (fun out i => out ++ [g ((x.drop i).take c.length)]) [] =
      List.ofFn (fun i : Fin k => g ((x.drop (i : ℕ)).take c.length)) := by
  intro g x c k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih, List.ofFn_succ', List.concat_eq_append]
      simp

end MPP.Solutions.Pnp139
