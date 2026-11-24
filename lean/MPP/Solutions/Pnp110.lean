import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp109

namespace MPP.Solutions.Pnp110

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (q : TM2.Stmt Γ Λ σ) (b : ℕ),
    TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 q ≤ b →
    ∀ (v : σ) (S S' : ∀ k, List (Γ k)), (∀ k, (S k).take (b + 1) = (S' k).take (b + 1)) →
      ∀ (k : K) (i : ℕ), (∀ j, j ≤ b + i → (S k)[j]? = (S' k)[j]?) →
        ((TM2.stepAux q v S).stk k)[i]? = ((TM2.stepAux q v S').stk k)[i]? := by
  intro K _ Γ Λ σ q b hb v S S' hS k i hcell
  obtain ⟨L, m, hm, h1, h2⟩ := MPP.Solutions.Pnp109.main K Γ Λ σ q b hb v S S' hS k
  rw [h1, h2]
  by_cases hi : i < L.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_drop, List.getElem?_drop]
    exact hcell _ (by omega)

end MPP.Solutions.Pnp110
