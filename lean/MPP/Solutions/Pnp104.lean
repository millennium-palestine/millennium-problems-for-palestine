import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp104

open MPP.PvsNP Computability Turing

theorem main : ∀ (L : Lang) (T : TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool L)
    (x : List Bool) (n : ℕ) (c : TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ),
    (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n]
      (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = some c →
    c.l = Option.none →
    ∀ k : ℕ, (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n + 1 + k]
      (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = Option.none := by
  intro L T x n c hn hc k
  have h1 : (some c).bind (TM2.step T.tm.m) = Option.none := by
    rcases c with ⟨_ | l, v, S⟩
    · rfl
    · exact absurd hc (by simp)
  have hstep : (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n + 1]
      (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = Option.none := by
    rw [Function.iterate_succ_apply', hn, h1]
  rw [show n + 1 + k = k + (n + 1) by omega, Function.iterate_add_apply, hstep]
  exact Function.iterate_fixed rfl k

end MPP.Solutions.Pnp104
