import Mathlib

namespace MPP.Solutions.Pnp248

theorem main : ∀ (B : ℕ → Bool × Bool → Prop) (P : ℕ → Bool → Bool → Prop) (X Y : ℕ → ℕ → Bool × Bool → Prop),
  (∀ (i : ℕ) (p : Bool × Bool), X i i p ↔ p.1 = p.2) → (∀ (i : ℕ) (p : Bool × Bool), Y i i p ↔ p.1 = p.2) →
  (∀ (i : ℕ) (p : Bool × Bool), X i (i + 1) p ↔ B i p) → (∀ (i : ℕ) (p : Bool × Bool), Y i (i + 1) p ↔ B i p) →
  (∀ (i j : ℕ) (p : Bool × Bool), i + 2 ≤ j → (X i j p ↔
    ((∃ u : Bool, P i u p.1 ∧ ∃ g' : Bool, X (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1)) ∨
     (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, X i k (p.1, g1) ∧ X k j (g1, p.2))))) →
  (∀ (i j : ℕ) (p : Bool × Bool), i + 2 ≤ j → (Y i j p ↔
    ((∃ u : Bool, P i u p.1 ∧ ∃ g' : Bool, Y (i + 1) (j - 1) (u, g') ∧ p.2 = !(g' && p.1)) ∨
     (∃ k : ℕ, i < k ∧ k < j ∧ ∃ g1 : Bool, Y i k (p.1, g1) ∧ Y k j (g1, p.2))))) →
  ∀ (i j : ℕ) (p : Bool × Bool), i < j → (X i j p ↔ Y i j p) := by
  intro B P X Y hXd hYd hXb hYb hXr hYr
  -- strong induction on the length of the interval
  have key : ∀ L : ℕ, ∀ i j : ℕ, ∀ p : Bool × Bool, j = i + L → (X i j p ↔ Y i j p) := by
    intro L
    induction L using Nat.strong_induction_on with
    | _ L ih =>
      intro i j p hL
      rcases Nat.lt_or_ge L 2 with hlt | hge
      · interval_cases L
        · subst hL
          simp only [hXd, hYd]
        · subst hL
          simp only [hXb, hYb]
      · have h2 : i + 2 ≤ j := by omega
        rw [hXr i j p h2, hYr i j p h2]
        have hmid : ∀ (u g' : Bool), X (i + 1) (j - 1) (u, g') ↔ Y (i + 1) (j - 1) (u, g') :=
          fun u g' => ih (j - 1 - (i + 1)) (by omega) (i + 1) (j - 1) (u, g') (by omega)
        have hsplitL : ∀ (k : ℕ) (g1 : Bool), i < k → k < j →
            (X i k (p.1, g1) ↔ Y i k (p.1, g1)) :=
          fun k g1 hik hkj => ih (k - i) (by omega) i k (p.1, g1) (by omega)
        have hsplitR : ∀ (k : ℕ) (g1 : Bool), i < k → k < j →
            (X k j (g1, p.2) ↔ Y k j (g1, p.2)) :=
          fun k g1 hik hkj => ih (j - k) (by omega) k j (g1, p.2) (by omega)
        apply or_congr
        · exact exists_congr fun u => and_congr Iff.rfl
            (exists_congr fun g' => and_congr (hmid u g') Iff.rfl)
        · exact exists_congr fun k => and_congr_right fun hik => and_congr_right fun hkj =>
            exists_congr fun g1 => and_congr (hsplitL k g1 hik hkj) (hsplitR k g1 hik hkj)
  intro i j p hij
  exact key (j - i) i j p (by omega)

end MPP.Solutions.Pnp248
