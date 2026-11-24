import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp105

open MPP.PvsNP Computability Turing

-- once the run from x0 has reached a halting configuration at step n, every later step is none
theorem dies_after_halt (tm : FinTM2) (x0 : TM2.Cfg tm.Γ tm.Λ tm.σ) (n : ℕ)
    (c : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (hn : (fun o : Option (TM2.Cfg tm.Γ tm.Λ tm.σ) => o.bind (TM2.step tm.m))^[n] (some x0) = some c)
    (hc : c.l = Option.none) (k : ℕ) :
    (fun o : Option (TM2.Cfg tm.Γ tm.Λ tm.σ) => o.bind (TM2.step tm.m))^[n + 1 + k] (some x0) =
      Option.none := by
  have h1 : (some c).bind (TM2.step tm.m) = Option.none := by
    rcases c with ⟨_ | l, v, S⟩
    · rfl
    · exact absurd hc (by simp)
  have hstep : (fun o : Option (TM2.Cfg tm.Γ tm.Λ tm.σ) => o.bind (TM2.step tm.m))^[n + 1] (some x0) =
      Option.none := by
    rw [Function.iterate_succ_apply', hn, h1]
  rw [show n + 1 + k = k + (n + 1) by omega, Function.iterate_add_apply, hstep]
  exact Function.iterate_fixed rfl k

theorem main : ∀ (L : Lang) (T : TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool L)
    (x : List Bool),
    ∃! n : ℕ, n ≤ T.time.eval x.length ∧
      ∃ c : TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ,
        (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n]
          (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = some c ∧ c.l = Option.none := by
  intro L T x
  have h := T.outputsFun x
  have hev : (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[h.steps]
      (some (initList T.tm (List.map T.inputAlphabet.invFun x))) =
        some (haltList T.tm (List.map T.outputAlphabet.invFun (encodeBool (L x)))) :=
    h.evals_in_steps
  refine ⟨h.steps, ⟨h.steps_le_m,
    haltList T.tm (List.map T.outputAlphabet.invFun (encodeBool (L x))), hev, rfl⟩, ?_⟩
  rintro m ⟨hm, d, hd, hdl⟩
  rcases lt_trichotomy m h.steps with hlt | heq | hgt
  · have hz := dies_after_halt T.tm _ m d hd hdl (h.steps - m - 1)
    rw [show m + 1 + (h.steps - m - 1) = h.steps by omega, hev] at hz
    exact absurd hz (Option.some_ne_none _)
  · exact heq
  · have hz := dies_after_halt T.tm _ h.steps _ hev rfl (m - h.steps - 1)
    rw [show h.steps + 1 + (m - h.steps - 1) = m by omega, hd] at hz
    exact absurd hz (Option.some_ne_none _)

end MPP.Solutions.Pnp105
