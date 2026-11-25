import Mathlib

namespace MPP.Solutions.Pnp193

theorem main : ∀ d : List ℤ, 0 < d.length → (∀ j ≤ d.length, 0 ≤ (d.take j).sum) → d.sum = 0 →
    ∃ m, 0 < m ∧ m ≤ d.length ∧ (d.take m).sum = 0 ∧ (∀ j, 0 < j → j < m → 0 < (d.take j).sum) ∧
      (∀ j ≤ d.length - m, 0 ≤ ((d.drop m).take j).sum) ∧ (d.drop m).sum = 0 := by
  intro d hpos hnn hsum0
  classical
  have hex : ∃ m, 0 < m ∧ (d.take m).sum = 0 :=
    ⟨d.length, hpos, by rw [List.take_length]; exact hsum0⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ d.length :=
    Nat.find_min' hex ⟨hpos, by rw [List.take_length]; exact hsum0⟩
  have hfirst : ∀ j, 0 < j → j < Nat.find hex → 0 < (d.take j).sum := by
    intro j hj1 hj2
    have hnz : (d.take j).sum ≠ 0 := fun h => Nat.find_min hex hj2 ⟨hj1, h⟩
    have h0 := hnn j (by omega)
    omega
  have htake : ∀ j, (d.take (Nat.find hex + j)).sum
      = (d.take (Nat.find hex)).sum + ((d.drop (Nat.find hex)).take j).sum := by
    intro j
    rw [List.take_add, List.sum_append]
  have hrest : ∀ j ≤ d.length - Nat.find hex, 0 ≤ ((d.drop (Nat.find hex)).take j).sum := by
    intro j hj
    have h1 := hnn (Nat.find hex + j) (by omega)
    have h2 := htake j
    rw [hspec.2] at h2
    omega
  have hdrop : (d.drop (Nat.find hex)).sum = 0 := by
    have h := List.sum_take_add_sum_drop d (Nat.find hex)
    rw [hspec.2] at h
    omega
  exact ⟨Nat.find hex, hspec.1, hle, hspec.2, hfirst, hrest, hdrop⟩

end MPP.Solutions.Pnp193
