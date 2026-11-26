import Mathlib

namespace MPP.Solutions.Pnp209

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n : ℕ) (r r' : List Bool), (∀ j, j < n + k → r.getD j false = r'.getD j false) →
    ∀ i, i < n → G ((List.range (k + 1)).map fun j => r.getD (i + j) false) =
      G ((List.range (k + 1)).map fun j => r'.getD (i + j) false) := by
  intro k G n r r' h i hi
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact h (i + j) (by omega)

end MPP.Solutions.Pnp209
