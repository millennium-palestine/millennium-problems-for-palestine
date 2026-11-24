import Mathlib

namespace MPP.Solutions.Bsd131

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [W.IsElliptic],
    Finite W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ p * p + 1 := by
  intro p _ W _
  have hf : Function.Injective (fun P : W.toAffine.Point => match P with
      | .zero => (none : Option (ZMod p × ZMod p))
      | .some (x := x) (y := y) _ => some (x, y)) := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
    · rfl
    · simp at hPQ
    · simp at hPQ
    · simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
      obtain ⟨rfl, rfl⟩ := hPQ
      rfl
  refine ⟨Finite.of_injective _ hf, ?_⟩
  have hle := Nat.card_le_card_of_injective _ hf
  have hopt : Nat.card (Option (ZMod p × ZMod p)) = p * p + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_prod, ZMod.card]
  omega

end MPP.Solutions.Bsd131
