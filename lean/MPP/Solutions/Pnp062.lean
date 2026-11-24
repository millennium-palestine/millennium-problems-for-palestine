import Mathlib

namespace MPP.Solutions.Pnp062

theorem main : ∀ s : List Bool → List Bool, (∀ z : List Bool, (s z).length = z.length + 1) →
    ∀ (k : ℕ) (z : List Bool), (s^[k] z).length = z.length + k := by
  intro s hs k
  induction k with
  | zero => intro z; simp
  | succ k ih =>
    intro z
    rw [Function.iterate_succ_apply, ih, hs]
    omega

end MPP.Solutions.Pnp062
