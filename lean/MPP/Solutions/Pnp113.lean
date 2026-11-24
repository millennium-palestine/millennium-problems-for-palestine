import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp113

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ),
    ∃ b : ℕ, ∀ l, TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 (M l) ≤ b := by
  intro K _ Γ Λ σ _ M
  let F : Λ → ℕ := fun l => TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih)
    (fun _ _ _ ih => ih) (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂)
    (fun _ => 0) 0 (M l)
  exact ⟨Finset.univ.sup F, fun l => Finset.le_sup (f := F) (Finset.mem_univ l)⟩

end MPP.Solutions.Pnp113
