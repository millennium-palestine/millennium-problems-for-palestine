import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp102

open MPP.PvsNP Computability Turing

theorem main : ∀ L : Lang, InP L → ∃ T : TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool L,
    ∀ x : List Bool, ∃ n : ℕ, n ≤ T.time.eval x.length ∧
      ∃ c : TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ,
        (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n]
          (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = some c ∧ c.l = Option.none := by
  intro L hL
  obtain ⟨T⟩ := hL
  refine ⟨T, fun x => ?_⟩
  have h := T.outputsFun x
  exact ⟨h.steps, h.steps_le_m,
    haltList T.tm (List.map T.outputAlphabet.invFun (encodeBool (L x))), h.evals_in_steps, rfl⟩

end MPP.Solutions.Pnp102
