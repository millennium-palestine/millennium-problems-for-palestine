import Mathlib

namespace MPP.Solutions.Pnp207

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n : ℕ) (r r' : List Bool), r.length = n → r'.length = n →
    ((∀ i, i < n → r'.getD i false = G ((List.range (k + 1)).map fun j => r.getD (i + j) false)) ↔
      r' = (List.range n).map fun i => G ((List.range (k + 1)).map fun j => r.getD (i + j) false)) := by
  intro k G n r r' _ hr'
  constructor
  · intro h
    apply List.ext_getElem
    · simp [hr']
    · intro i h1 h2
      have hi : i < n := by simpa [hr'] using h1
      rw [List.getElem_map, List.getElem_range]
      have := h i hi
      rw [List.getD_eq_getElem _ _ h1] at this
      exact this
  · intro h i hi
    subst h
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

end MPP.Solutions.Pnp207
