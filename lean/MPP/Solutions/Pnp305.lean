import Mathlib

namespace MPP.Solutions.Pnp305

theorem main : ∀ (w : List Bool) (n : ℕ),
    (List.ofFn (fun i : Fin n => w.getD i false)).length = n ∧
      ∀ i : ℕ, i < n → (List.ofFn (fun i : Fin n => w.getD i false)).getD i false = w.getD i false := by
  intro w n
  refine ⟨List.length_ofFn, fun i hi => ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

end MPP.Solutions.Pnp305
