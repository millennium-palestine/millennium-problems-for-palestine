import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp107

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ),
    TM2.Stmt.rec (motive := fun _ => Prop) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ _ => False) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => ih₁ ∧ ih₂) (fun _ => True) True q →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, (S k).head? = (S' k).head?) →
      ∀ k, ∃ L : List (Γ k), (TM2.stepAux q v S).stk k = L ++ S k ∧
        (TM2.stepAux q v S').stk k = L ++ S' k := by
  intro K _ Γ Λ σ q
  induction q with
  | push k f q ih =>
    intro hq v S S' hS j
    have hS1 : ∀ i, (Function.update S k (f v :: S k) i).head? =
        (Function.update S' k (f v :: S' k) i).head? := by
      intro i
      by_cases h : i = k
      · subst h; simp
      · simp only [Function.update_of_ne h, hS i]
    by_cases hj : j = k
    · subst hj
      obtain ⟨L, h1, h2⟩ := ih hq v _ _ hS1 j
      refine ⟨L ++ [f v], ?_, ?_⟩
      · simp only [TM2.stepAux]
        rw [h1]
        simp
      · simp only [TM2.stepAux]
        rw [h2]
        simp
    · obtain ⟨L, h1, h2⟩ := ih hq v _ _ hS1 j
      refine ⟨L, ?_, ?_⟩
      · simp only [TM2.stepAux]
        rw [h1]
        simp [Function.update_of_ne hj]
      · simp only [TM2.stepAux]
        rw [h2]
        simp [Function.update_of_ne hj]
  | peek k f q ih =>
    intro hq v S S' hS j
    have hv : f v (S k).head? = f v (S' k).head? := by rw [hS k]
    simp only [TM2.stepAux]
    rw [hv]
    exact ih hq _ S S' hS j
  | pop k f q ih =>
    intro hq
    exact (hq : False).elim
  | load a q ih =>
    intro hq v S S' hS j
    simp only [TM2.stepAux]
    exact ih hq _ S S' hS j
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro hq v S S' hS j
    obtain ⟨h1, h2⟩ := hq
    simp only [TM2.stepAux]
    cases hfv : f v
    · simp only [cond_false]
      exact ih₂ h2 v S S' hS j
    · simp only [cond_true]
      exact ih₁ h1 v S S' hS j
  | goto f =>
    intro _ v S S' hS j
    exact ⟨[], rfl, rfl⟩
  | halt =>
    intro _ v S S' hS j
    exact ⟨[], rfl, rfl⟩

end MPP.Solutions.Pnp107
