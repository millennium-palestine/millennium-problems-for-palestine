import Mathlib

namespace MPP.Solutions.Bsd250

theorem main : ∀ (A : Type) [CommRing A] [IsDomain A] (B Y : ℤ → A),
    (∀ m : ℤ, 2 ≤ m → Y m ≠ 0) →
    (∀ m : ℤ, 2 ≤ m → Y m * B (m + 1) = Y (m + 1) * B m) →
    B 2 = 0 →
    ∀ m : ℤ, 2 ≤ m → B m = 0 := by
  intro A _ _ B Y hY hT h2 m hm
  induction m, hm using Int.le_induction with
  | base => exact h2
  | succ k hk ih =>
    have h := hT k hk
    rw [ih, mul_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hY k hk)
    · exact h'

end MPP.Solutions.Bsd250
