import Mathlib

namespace MPP.Solutions.Pnp250

theorem main : ∀ (B : ℕ → Bool × Bool → Prop) (U D : ℕ → Prop) (M : ℕ → ℕ → Prop) (P : ℕ → Bool → Bool → Prop) (X Y : ℕ → ℕ → Bool × Bool → Prop),
    (∀ (i : ℕ) (p : Bool × Bool), X i i p ↔ p.1 = p.2) → (∀ (i : ℕ) (p : Bool × Bool), Y i i p ↔ p.1 = p.2) →
    (∀ (i : ℕ) (p : Bool × Bool), X i (i + 1) p ↔ B i p) → (∀ (i : ℕ) (p : Bool × Bool), Y i (i + 1) p ↔ B i p) →
    (∀ (i j : ℕ) (p : Bool × Bool), i + 2 ≤ j → (X i j p ↔
      ((U i ∧ ∃ u : Bool, P i u p.1 ∧ D (j - 1) ∧ M (i + 1) (j - 1) ∧ ∃ g' : Bool, X (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1)) ∨
       (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, X i k (p.1, g1) ∧ X k j (g1, p.2))))) →
    (∀ (i j : ℕ) (p : Bool × Bool), i + 2 ≤ j → (Y i j p ↔
      ((U i ∧ ∃ u : Bool, P i u p.1 ∧ D (j - 1) ∧ M (i + 1) (j - 1) ∧ ∃ g' : Bool, Y (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1)) ∨
       (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, Y i k (p.1, g1) ∧ Y k j (g1, p.2))))) →
    ∀ (i j : ℕ) (p : Bool × Bool), i < j → (X i j p ↔ Y i j p) := by
  intro B U D M P X Y hX0 hY0 hX1 hY1 hX hY
  have key : ∀ n i j p, j - i = n → i < j → (X i j p ↔ Y i j p) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j p hn hij
      by_cases h1 : j = i + 1
      · subst h1
        exact (hX1 i p).trans (hY1 i p).symm
      · have h2 : i + 2 ≤ j := by omega
        have hmid : ∀ u g', X (i + 1) (j - 1) (u, g') ↔ Y (i + 1) (j - 1) (u, g') := by
          intro u g'
          rcases Nat.lt_or_ge (i + 1) (j - 1) with h | h
          · exact ih (j - 1 - (i + 1)) (by omega) (i + 1) (j - 1) (u, g') rfl h
          · have he : i + 1 = j - 1 := by omega
            rw [← he, hX0, hY0]
        rw [hX i j p h2, hY i j p h2]
        constructor
        · rintro (⟨hU, u, hu, hD, hM, g', hg', hg⟩ | ⟨k, hk1, hk2, g1, hA, hB⟩)
          · exact Or.inl ⟨hU, u, hu, hD, hM, g', (hmid u g').1 hg', hg⟩
          · exact Or.inr ⟨k, hk1, hk2, g1,
              (ih (k - i) (by omega) i k (p.1, g1) rfl hk1).1 hA,
              (ih (j - k) (by omega) k j (g1, p.2) rfl hk2).1 hB⟩
        · rintro (⟨hU, u, hu, hD, hM, g', hg', hg⟩ | ⟨k, hk1, hk2, g1, hA, hB⟩)
          · exact Or.inl ⟨hU, u, hu, hD, hM, g', (hmid u g').2 hg', hg⟩
          · exact Or.inr ⟨k, hk1, hk2, g1,
              (ih (k - i) (by omega) i k (p.1, g1) rfl hk1).2 hA,
              (ih (j - k) (by omega) k j (g1, p.2) rfl hk2).2 hB⟩
  intro i j p hij
  exact key _ i j p rfl hij

end MPP.Solutions.Pnp250
