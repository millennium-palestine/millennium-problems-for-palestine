import Mathlib

namespace MPP.Solutions.Pnp253

theorem main : ∀ s w : List Bool → List Bool,
    (∀ z : List Bool, w (s z) = w z) →
    (∀ z : List Bool, (s z).length ≤ z.length + (w z).length) →
    ∀ (m : ℕ) (z : List Bool), (s^[m] z).length ≤ z.length + m * (w z).length := by
  intro s w hw hs m
  induction m with
  | zero => intro z; simp
  | succ m ih =>
    intro z
    rw [Function.iterate_succ_apply]
    have h1 := ih (s z)
    rw [hw z] at h1
    have h2 := hs z
    rw [Nat.succ_mul]
    linarith

end MPP.Solutions.Pnp253
