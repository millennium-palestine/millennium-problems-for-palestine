import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp112
import MPP.Solutions.Pnp113

namespace MPP.Solutions.Pnp114

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ),
    ∃ b : ℕ, ∀ (t n : ℕ) (c c' : TM2.Cfg Γ Λ σ), c.l = c'.l → c.var = c'.var →
      (∀ k, (c.stk k).take (n + t * b + 1) = (c'.stk k).take (n + t * b + 1)) →
      ((fun o : Option (TM2.Cfg Γ Λ σ) => o.bind (TM2.step M))^[t] (some c)).map
          (fun d => (d.l, d.var, fun k => (d.stk k).take (n + 1))) =
        ((fun o : Option (TM2.Cfg Γ Λ σ) => o.bind (TM2.step M))^[t] (some c')).map
          (fun d => (d.l, d.var, fun k => (d.stk k).take (n + 1))) := by
  intro K _ Γ Λ σ _ M
  obtain ⟨b, hb⟩ := MPP.Solutions.Pnp113.main K Γ Λ σ M
  exact ⟨b, fun t n c c' hl hvar hS => MPP.Solutions.Pnp112.main K Γ Λ σ M b hb t n c c' hl hvar hS⟩

end MPP.Solutions.Pnp114
