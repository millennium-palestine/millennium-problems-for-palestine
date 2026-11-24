import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp106

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ),
    TM2.Stmt.rec (motive := fun _ => Prop) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ _ => False) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => ih₁ ∧ ih₂) (fun _ => True) True q →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, (S k).head? = (S' k).head?) →
      (TM2.stepAux q v S).l = (TM2.stepAux q v S').l ∧
      (TM2.stepAux q v S).var = (TM2.stepAux q v S').var ∧
      ∀ k, ((TM2.stepAux q v S).stk k).head? = ((TM2.stepAux q v S').stk k).head? := by
  intro K _ Γ Λ σ q
  induction q with
  | push k f q ih =>
    intro hq v S S' hS
    simp only [TM2.stepAux]
    refine ih hq _ _ _ ?_
    intro j
    by_cases h : j = k
    · subst h; simp
    · simp only [Function.update_of_ne h, hS j]
  | peek k f q ih =>
    intro hq v S S' hS
    have hv : f v (S k).head? = f v (S' k).head? := by rw [hS k]
    simp only [TM2.stepAux]
    rw [hv]
    exact ih hq _ S S' hS
  | pop k f q ih =>
    intro hq
    exact (hq : False).elim
  | load a q ih =>
    intro hq v S S' hS
    simp only [TM2.stepAux]
    exact ih hq _ S S' hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro hq v S S' hS
    obtain ⟨h1, h2⟩ := hq
    simp only [TM2.stepAux]
    cases hfv : f v
    · simp only [cond_false]
      exact ih₂ h2 v S S' hS
    · simp only [cond_true]
      exact ih₁ h1 v S S' hS
  | goto f =>
    intro _ v S S' hS
    exact ⟨rfl, rfl, hS⟩
  | halt =>
    intro _ v S S' hS
    exact ⟨rfl, rfl, hS⟩

end MPP.Solutions.Pnp106
