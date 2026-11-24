import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp108
import MPP.Solutions.Pnp110

namespace MPP.Solutions.Pnp111

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ) (b n : ℕ),
    TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 q ≤ b →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, ∀ j, j ≤ b + n → (S k)[j]? = (S' k)[j]?) →
      (TM2.stepAux q v S).l = (TM2.stepAux q v S').l ∧
      (TM2.stepAux q v S).var = (TM2.stepAux q v S').var ∧
      ∀ k, ∀ i, i ≤ n → ((TM2.stepAux q v S).stk k)[i]? = ((TM2.stepAux q v S').stk k)[i]? := by
  intro K _ Γ Λ σ q b n hb v S S' hS
  have hT : ∀ k, (S k).take (b + 1) = (S' k).take (b + 1) := by
    intro k
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with h
    · exact hS k j (by omega)
    · rfl
  obtain ⟨hl, hvar, -⟩ := MPP.Solutions.Pnp108.main K Γ Λ σ q b hb v S S' hT
  refine ⟨hl, hvar, ?_⟩
  intro k i hi
  exact MPP.Solutions.Pnp110.main K Γ Λ σ q b hb v S S' hT k i (fun j hj => hS k j (by omega))

end MPP.Solutions.Pnp111
