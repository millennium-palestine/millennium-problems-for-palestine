import Mathlib

namespace MPP.Solutions.Pnp210

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n t : ℕ) (r r' : List Bool), r.length = n → r'.length = n →
    ∀ i, (∀ j, i ≤ j → j ≤ i + k * t → r.getD j false = r'.getD j false) →
      ((fun q : List Bool => (List.range n).map fun i =>
        G ((List.range (k + 1)).map fun j => q.getD (i + j) false))^[t] r).getD i false =
      ((fun q : List Bool => (List.range n).map fun i =>
        G ((List.range (k + 1)).map fun j => q.getD (i + j) false))^[t] r').getD i false := by
  intro k G n t
  induction t with
  | zero =>
    intro r r' _ _ i h
    simpa using h i le_rfl (by simp)
  | succ t ih =>
    intro r r' hr hr' i h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    apply ih _ _ (by simp) (by simp) i
    intro j hj1 hj2
    by_cases hjn : n ≤ j
    · simp [hjn]
    · have hjl : j < n := by omega
      have hk : k * (t + 1) = k * t + k := by ring
      rw [List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map, List.getElem_range,
        List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map, List.getElem_range]
      congr 1
      apply List.map_congr_left
      intro m hm
      rw [List.mem_range] at hm
      exact h (j + m) (by omega) (by omega)

end MPP.Solutions.Pnp210
