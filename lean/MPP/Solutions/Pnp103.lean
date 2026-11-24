import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp103

open MPP.PvsNP Computability Turing

theorem main : ∀ (tm : FinTM2) (c : TM2.Cfg tm.Γ tm.Λ tm.σ), c.l = Option.none → ∀ n : ℕ,
    (fun o : Option (TM2.Cfg tm.Γ tm.Λ tm.σ) => o.bind (TM2.step tm.m))^[n + 1] (some c) =
      Option.none := by
  intro tm c hc n
  have h1 : (some c).bind (TM2.step tm.m) = Option.none := by
    rcases c with ⟨_ | l, v, S⟩
    · rfl
    · exact absurd hc (by simp)
  rw [Function.iterate_succ_apply, h1]
  exact Function.iterate_fixed rfl n

end MPP.Solutions.Pnp103
