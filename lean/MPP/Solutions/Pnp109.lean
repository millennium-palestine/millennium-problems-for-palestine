import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp109

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ) (b : ℕ),
    TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 q ≤ b →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, (S k).take (b + 1) = (S' k).take (b + 1)) →
      ∀ k, ∃ (L : List (Γ k)) (m : ℕ), m ≤ b ∧
        (TM2.stepAux q v S).stk k = L ++ (S k).drop m ∧
        (TM2.stepAux q v S').stk k = L ++ (S' k).drop m := by
  intro K _ Γ Λ σ q
  have key : ∀ (X : Type) (l l' : List X) (n : ℕ), l.take (n + 1) = l'.take (n + 1) →
      l.take n = l'.take n := by
    intro X l l' n h
    have := congrArg (List.take n) h
    simpa [List.take_take] using this
  have headEq : ∀ (X : Type) (l l' : List X) (n : ℕ), l.take (n + 1) = l'.take (n + 1) →
      l.head? = l'.head? := by
    intro X l l' n h
    cases l <;> cases l' <;> simp_all
  have tailEq : ∀ (X : Type) (l l' : List X) (n : ℕ), l.take (n + 2) = l'.take (n + 2) →
      l.tail.take (n + 1) = l'.tail.take (n + 1) := by
    intro X l l' n h
    cases l <;> cases l' <;> simp_all [List.take_succ_cons]
  have dropTail : ∀ (X : Type) (l : List X) (n : ℕ), l.drop (n + 1) = l.tail.drop n := by
    intro X l n
    cases l <;> simp
  induction q with
  | push k f q ih =>
    intro b hb v S S' hS j
    have hS1 : ∀ i, (Function.update S k (f v :: S k) i).take (b + 1) =
        (Function.update S' k (f v :: S' k) i).take (b + 1) := by
      intro i
      by_cases h : i = k
      · subst h
        simp only [Function.update_self, List.take_succ_cons]
        rw [key _ _ _ _ (hS i)]
      · simp only [Function.update_of_ne h]
        exact hS i
    simp only [TM2.stepAux]
    obtain ⟨L, m, hm, h1, h2⟩ := ih b hb v _ _ hS1 j
    by_cases h : j = k
    · subst h
      simp only [Function.update_self] at h1 h2
      rcases m with _ | m0
      · refine ⟨L ++ [f v], 0, by omega, ?_, ?_⟩
        · rw [h1]; simp
        · rw [h2]; simp
      · refine ⟨L, m0, by omega, ?_, ?_⟩
        · rw [h1]; simp [List.drop_succ_cons]
        · rw [h2]; simp [List.drop_succ_cons]
    · simp only [Function.update_of_ne h] at h1 h2
      exact ⟨L, m, hm, h1, h2⟩
  | peek k f q ih =>
    intro b hb v S S' hS j
    have hv : f v (S k).head? = f v (S' k).head? := by
      rw [headEq _ _ _ _ (hS k)]
    simp only [TM2.stepAux]
    rw [hv]
    exact ih b hb _ S S' hS j
  | pop k f q ih =>
    intro b hb v S S' hS j
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := by
      dsimp only at hb
      exact ⟨b - 1, by omega⟩
    have hv : f v (S k).head? = f v (S' k).head? := by
      rw [headEq _ _ _ _ (hS k)]
    have hS1 : ∀ i, (Function.update S k (S k).tail i).take (c + 1) =
        (Function.update S' k (S' k).tail i).take (c + 1) := by
      intro i
      by_cases h : i = k
      · subst h
        simp only [Function.update_self]
        exact tailEq _ _ _ _ (hS i)
      · simp only [Function.update_of_ne h]
        exact key _ _ _ _ (hS i)
    have hc : TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
        (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 q ≤ c := by
      dsimp only at hb
      omega
    simp only [TM2.stepAux]
    rw [hv]
    obtain ⟨L, m, hm, h1, h2⟩ := ih c hc (f v (S' k).head?) _ _ hS1 j
    by_cases h : j = k
    · subst h
      simp only [Function.update_self] at h1 h2
      refine ⟨L, m + 1, by omega, ?_, ?_⟩
      · rw [h1, dropTail]
      · rw [h2, dropTail]
    · simp only [Function.update_of_ne h] at h1 h2
      exact ⟨L, m, by omega, h1, h2⟩
  | load a q ih =>
    intro b hb v S S' hS j
    simp only [TM2.stepAux]
    exact ih b hb _ S S' hS j
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro b hb v S S' hS j
    dsimp only at hb
    have h1 := le_trans (le_max_left _ _) hb
    have h2 := le_trans (le_max_right _ _) hb
    simp only [TM2.stepAux]
    cases hfv : f v
    · simp only [cond_false]
      exact ih₂ b h2 v S S' hS j
    · simp only [cond_true]
      exact ih₁ b h1 v S S' hS j
  | goto f =>
    intro b _ v S S' hS j
    refine ⟨[], 0, Nat.zero_le _, ?_, ?_⟩ <;> simp [TM2.stepAux]
  | halt =>
    intro b _ v S S' hS j
    refine ⟨[], 0, Nat.zero_le _, ?_, ?_⟩ <;> simp [TM2.stepAux]

end MPP.Solutions.Pnp109
