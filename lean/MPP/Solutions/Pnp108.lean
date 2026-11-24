import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp108

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ) (b : ℕ),
    TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 q ≤ b →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, (S k).take (b + 1) = (S' k).take (b + 1)) →
      (TM2.stepAux q v S).l = (TM2.stepAux q v S').l ∧
      (TM2.stepAux q v S).var = (TM2.stepAux q v S').var ∧
      ∀ k, ((TM2.stepAux q v S).stk k).head? = ((TM2.stepAux q v S').stk k).head? := by
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
  induction q with
  | push k f q ih =>
    intro b hb v S S' hS
    simp only [TM2.stepAux]
    refine ih _ hb _ _ _ ?_
    intro j
    by_cases h : j = k
    · subst h
      simp only [Function.update_self, List.take_succ_cons]
      rw [key _ _ _ _ (hS j)]
    · simp only [Function.update_of_ne h, hS j]
  | peek k f q ih =>
    intro b hb v S S' hS
    have hv : f v (S k).head? = f v (S' k).head? := by
      rw [headEq _ _ _ _ (hS k)]
    simp only [TM2.stepAux]
    rw [hv]
    exact ih _ hb _ S S' hS
  | pop k f q ih =>
    intro b hb v S S' hS
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := by
      dsimp only at hb
      exact ⟨b - 1, by omega⟩
    have hv : f v (S k).head? = f v (S' k).head? := by
      rw [headEq _ _ _ _ (hS k)]
    simp only [TM2.stepAux]
    rw [hv]
    refine ih c ?_ _ _ _ ?_
    · dsimp only at hb
      omega
    · intro j
      by_cases h : j = k
      · subst h
        simp only [Function.update_self]
        exact tailEq _ _ _ _ (hS j)
      · simp only [Function.update_of_ne h]
        exact key _ _ _ _ (hS j)
  | load a q ih =>
    intro b hb v S S' hS
    simp only [TM2.stepAux]
    exact ih _ hb _ S S' hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro b hb v S S' hS
    dsimp only at hb
    have h1 := le_trans (le_max_left _ _) hb
    have h2 := le_trans (le_max_right _ _) hb
    simp only [TM2.stepAux]
    cases hfv : f v
    · simp only [cond_false]
      exact ih₂ _ h2 v S S' hS
    · simp only [cond_true]
      exact ih₁ _ h1 v S S' hS
  | goto f =>
    intro b _ v S S' hS
    exact ⟨rfl, rfl, fun k => headEq _ _ _ _ (hS k)⟩
  | halt =>
    intro b _ v S S' hS
    exact ⟨rfl, rfl, fun k => headEq _ _ _ _ (hS k)⟩

end MPP.Solutions.Pnp108
