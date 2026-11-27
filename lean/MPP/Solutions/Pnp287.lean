import Mathlib

namespace MPP.Solutions.Pnp287

theorem main : ∀ (P : ℕ → ℕ → Bool → Bool → Prop) (X : ℕ → ℕ → Bool × Bool → Prop) (c : ℕ → ℕ → Bool × Bool → Bool),
    (∀ i : ℕ, ∀ r : Bool × Bool, X i i r ↔ r.1 = r.2) →
    (∀ i : ℕ, ∀ r : Bool × Bool, c i i r = true ↔ r.1 = r.2) →
    (∀ i : ℕ, ∀ r : Bool × Bool, c i (i + 1) r = true ↔ X i (i + 1) r) →
    (∀ i j : ℕ, ∀ r : Bool × Bool, i + 2 ≤ j → (X i j r ↔
      ((∃ u : Bool, P i j u r.1 ∧ ∃ g' : Bool, X (i + 1) (j - 1) (u, g') ∧ r.2 = !(g' && r.1)) ∨
       (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, X i k (r.1, g1) ∧ X k j (g1, r.2))))) →
    (∀ i j : ℕ, ∀ r : Bool × Bool, i + 2 ≤ j → (c i j r = true ↔
      ((∃ u : Bool, P i j u r.1 ∧ ∃ g' : Bool, c (i + 1) (j - 1) (u, g') = true ∧ r.2 = !(g' && r.1)) ∨
       (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, c i k (r.1, g1) = true ∧ c k j (g1, r.2) = true)))) →
    ∀ i j : ℕ, ∀ r : Bool × Bool, i ≤ j → (c i j r = true ↔ X i j r) := by
  intro P X c H1 H2 H3 H4 H5
  -- every interval of length at most n agrees, by induction on n
  have key : ∀ n : ℕ, ∀ i j : ℕ, ∀ r : Bool × Bool, j - i ≤ n → i ≤ j → (c i j r = true ↔ X i j r) := by
    intro n
    induction n with
    | zero =>
      intro i j r hd hij
      have hj : j = i := by omega
      subst hj
      rw [H2 j r, H1 j r]
    | succ n ih =>
      intro i j r hd hij
      by_cases hle : j - i ≤ n
      · exact ih i j r hle hij
      · by_cases hj : j = i + 1
        · subst hj
          exact H3 i r
        · have hij2 : i + 2 ≤ j := by omega
          rw [H5 i j r hij2, H4 i j r hij2]
          constructor
          · rintro (⟨u, hP, g', hc, hr⟩ | ⟨k, hik, hkj, g1, h1, h2⟩)
            · exact Or.inl ⟨u, hP, g', (ih (i + 1) (j - 1) (u, g') (by omega) (by omega)).1 hc, hr⟩
            · exact Or.inr ⟨k, hik, hkj, g1, (ih i k (r.1, g1) (by omega) (by omega)).1 h1,
                (ih k j (g1, r.2) (by omega) (by omega)).1 h2⟩
          · rintro (⟨u, hP, g', hX, hr⟩ | ⟨k, hik, hkj, g1, h1, h2⟩)
            · exact Or.inl ⟨u, hP, g', (ih (i + 1) (j - 1) (u, g') (by omega) (by omega)).2 hX, hr⟩
            · exact Or.inr ⟨k, hik, hkj, g1, (ih i k (r.1, g1) (by omega) (by omega)).2 h1,
                (ih k j (g1, r.2) (by omega) (by omega)).2 h2⟩
  intro i j r hij
  exact key (j - i) i j r le_rfl hij

end MPP.Solutions.Pnp287
