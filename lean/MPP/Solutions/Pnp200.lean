import Mathlib

namespace MPP.Solutions.Pnp200

theorem main : ∀ (k : ℕ) (G : List Bool → Bool) (n T : ℕ) (rows : ℕ → List Bool), (∀ t, (rows t).length = n) →
    ((∀ t, t < T → rows (t + 1) = (List.range n).map fun i => G ((List.range (k + 1)).map fun j => (rows t).getD (i + j) false)) ↔
      (∀ t, t ≤ T → rows t = Nat.iterate (fun r : List Bool => (List.range n).map fun i => G ((List.range (k + 1)).map fun j => r.getD (i + j) false)) t (rows 0))) := by
  intro k G n T rows _
  constructor
  · intro h t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      rw [h t (by omega), Function.iterate_succ_apply', ih (by omega)]
  · intro h t ht
    have h1 := h t (by omega)
    have h2 := h (t + 1) (by omega)
    rw [h2, Function.iterate_succ_apply', ← h1]

end MPP.Solutions.Pnp200
