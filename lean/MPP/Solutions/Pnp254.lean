import Mathlib

namespace MPP.Solutions.Pnp254

theorem main : ∀ (s w : List Bool → List Bool) (c : ℕ),
    (∀ z : List Bool, w (s z) = w z) →
    (∀ z : List Bool, (s z).length ≤ z.length + (w z).length) →
    (∀ z : List Bool, (w z).length ≤ z.length + c) →
    ∀ (m : ℕ) (z : List Bool), (s^[m] z).length ≤ z.length + m * (z.length + c) := by
  intro s w c hw hs hc
  have key : ∀ (m : ℕ) (z : List Bool), (s^[m] z).length ≤ z.length + m * (w z).length := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      rw [Function.iterate_succ_apply]
      have h1 := ih (s z)
      rw [hw z] at h1
      have h2 := hs z
      rw [Nat.succ_mul]
      omega
  intro m z
  have h3 : m * (w z).length ≤ m * (z.length + c) := Nat.mul_le_mul_left m (hc z)
  have h4 := key m z
  omega

end MPP.Solutions.Pnp254
