import Mathlib

namespace MPP.Solutions.Pnp199

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n : ℕ) (r r' : List Bool), r.length = n → r'.length = n →
    ((∀ i, i < n → r'.getD i false = G ((List.range (k + 1)).map fun j => r.getD (i + j) false)) ↔
      r' = (List.range n).map fun i => G ((List.range (k + 1)).map fun j => r.getD (i + j) false)) := by
  intro k G n r r' hr hr'
  constructor
  · intro h
    apply List.ext_getElem
    · simp [hr']
    · intro i h1 h2
      have hi : i < n := by simpa [hr'] using h1
      rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem r' false h1]
      exact h i hi
  · intro h i hi
    subst h
    simp [List.getD_eq_getElem?_getD, hi]

end MPP.Solutions.Pnp199
