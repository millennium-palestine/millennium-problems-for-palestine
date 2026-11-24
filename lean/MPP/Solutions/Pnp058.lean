import Mathlib

namespace MPP.Solutions.Pnp058

theorem main : ∀ (E : List Bool → Bool) (N : ℕ) (step : List Bool → List Bool),
    E [] = true →
    (∀ u : List Bool, u.length < N → E u = true → E (u ++ [false]) = true ∨ E (u ++ [true]) = true) →
    (∀ u : List Bool, step u = if E (u ++ [false]) = true then u ++ [false] else u ++ [true]) →
    (step^[N] []).length = N ∧ E (step^[N] []) = true := by
  intro E N step h0 hext hstep
  have key : ∀ k : ℕ, k ≤ N → (step^[k] []).length = k ∧ E (step^[k] []) = true := by
    intro k
    induction k with
    | zero => intro _; exact ⟨rfl, h0⟩
    | succ k ih =>
      intro hk
      obtain ⟨hlen, hE⟩ := ih (by omega)
      have hlt : (step^[k] []).length < N := by rw [hlen]; omega
      rw [Function.iterate_succ_apply', hstep]
      by_cases h : E ((step^[k] []) ++ [false]) = true
      · rw [if_pos h]
        exact ⟨by simp [hlen], h⟩
      · rw [if_neg h]
        have ht : E ((step^[k] []) ++ [true]) = true := (hext _ hlt hE).resolve_left h
        exact ⟨by simp [hlen], ht⟩
  exact key N le_rfl

end MPP.Solutions.Pnp058
