import Mathlib

namespace MPP.Solutions.Bsd021

theorem main : ∀ p k : ℕ, p.Prime → (p ^ k).divisors.card = k + 1 := by
  intro p k hp
  rw [Nat.divisors_prime_pow hp k, Finset.card_map, Finset.card_range]

end MPP.Solutions.Bsd021
