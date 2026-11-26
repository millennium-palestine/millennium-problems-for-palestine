import Mathlib

namespace MPP.Solutions.Pnp208

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n T : ℕ) (r : ℕ → List Bool), (r 0).length = n →
    (∀ t, t < T → (r (t + 1)).length = n ∧
      ∀ i, i < n → (r (t + 1)).getD i false = G ((List.range (k + 1)).map fun j => (r t).getD (i + j) false)) →
    ∀ t, t ≤ T → r t = (fun q : List Bool => (List.range n).map fun i =>
      G ((List.range (k + 1)).map fun j => q.getD (i + j) false))^[t] (r 0) := by
  intro k G n T r _ hstep t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    obtain ⟨hlen, hent⟩ := hstep t (by omega)
    rw [Function.iterate_succ_apply', ← hprev]
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      have hi : i < n := by simpa [hlen] using h1
      rw [List.getElem_map, List.getElem_range]
      have := hent i hi
      rw [List.getD_eq_getElem _ _ h1] at this
      exact this

end MPP.Solutions.Pnp208
