import Mathlib

namespace MPP.Solutions.Pnp306

theorem main : ∀ (C : List (List (ℕ × Bool))) (n : ℕ),
    (∀ c ∈ C, ∀ l ∈ c, l.1 < n) →
    (∃ w : List Bool, ∀ c ∈ C, ∃ l ∈ c, w.getD l.1 false = l.2) →
    ∃ v : List Bool, v.length = n ∧ ∀ c ∈ C, ∃ l ∈ c, v.getD l.1 false = l.2 := by
  intro C n hC hex
  obtain ⟨w, hw⟩ := hex
  refine ⟨List.ofFn (fun i : Fin n => w.getD i false), List.length_ofFn, fun c hc => ?_⟩
  obtain ⟨l, hl, hwl⟩ := hw c hc
  refine ⟨l, hl, ?_⟩
  have key : (List.ofFn (fun i : Fin n => w.getD i false)).getD l.1 false = w.getD l.1 false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hC c hc l hl]
  rw [key]
  exact hwl

end MPP.Solutions.Pnp306
