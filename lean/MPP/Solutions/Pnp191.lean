import Mathlib

namespace MPP.Solutions.Pnp191

theorem main : ∀ d : List ℤ, 0 < d.length → (∀ j ≤ d.length, 0 ≤ (d.take j).sum) → d.sum = 0 →
    ∃ m, 0 < m ∧ m ≤ d.length ∧ (d.take m).sum = 0 ∧ ∀ j, 0 < j → j < m → 0 < (d.take j).sum := by
  intro d hpos hnn hsum0
  classical
  have hex : ∃ m, 0 < m ∧ (d.take m).sum = 0 :=
    ⟨d.length, hpos, by rw [List.take_length]; exact hsum0⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ d.length :=
    Nat.find_min' hex ⟨hpos, by rw [List.take_length]; exact hsum0⟩
  refine ⟨Nat.find hex, hspec.1, hle, hspec.2, fun j hj1 hj2 => ?_⟩
  have hnz : (d.take j).sum ≠ 0 := fun h => Nat.find_min hex hj2 ⟨hj1, h⟩
  have h0 := hnn j (by omega)
  omega

end MPP.Solutions.Pnp191
