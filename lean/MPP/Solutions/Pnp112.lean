import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp111

namespace MPP.Solutions.Pnp112

open Computability Turing

theorem main : ∀ (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) (M : Λ → TM2.Stmt Γ Λ σ) (b : ℕ),
    (∀ l, TM2.Stmt.rec (motive := fun _ => ℕ) (fun _ _ _ ih => ih) (fun _ _ _ ih => ih)
      (fun _ _ _ ih => ih + 1) (fun _ _ ih => ih) (fun _ _ _ ih₁ ih₂ => max ih₁ ih₂) (fun _ => 0) 0 (M l) ≤ b) →
    ∀ (t n : ℕ) (c c' : TM2.Cfg Γ Λ σ), c.l = c'.l → c.var = c'.var →
      (∀ k, (c.stk k).take (n + t * b + 1) = (c'.stk k).take (n + t * b + 1)) →
      ((fun o : Option (TM2.Cfg Γ Λ σ) => o.bind (TM2.step M))^[t] (some c)).map
          (fun d => (d.l, d.var, fun k => (d.stk k).take (n + 1))) =
        ((fun o : Option (TM2.Cfg Γ Λ σ) => o.bind (TM2.step M))^[t] (some c')).map
          (fun d => (d.l, d.var, fun k => (d.stk k).take (n + 1))) := by
  intro K _ Γ Λ σ M b hM
  -- one step of a configuration with a label
  have hstep : ∀ (c : TM2.Cfg Γ Λ σ) (l : Λ), c.l = some l →
      TM2.step M c = some (TM2.stepAux (M l) c.var c.stk) := by
    intro c l h
    obtain ⟨cl, cv, cs⟩ := c
    cases cl with
    | none => simp at h
    | some l' =>
      simp only [Option.some.injEq] at h
      subst h
      rfl
  -- a configuration without a label takes no step
  have hnone : ∀ c : TM2.Cfg Γ Λ σ, c.l = none → TM2.step M c = none := by
    intro c h
    obtain ⟨cl, cv, cs⟩ := c
    cases cl with
    | none => rfl
    | some l' => simp at h
  -- equal blocks: take of an index-form equality
  have toTake : ∀ (X : Type) (l l' : List X) (m : ℕ), (∀ i, i < m → l[i]? = l'[i]?) →
      l.take m = l'.take m := by
    intro X l l' m h
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hj
    · exact h j hj
    · rfl
  have fromTake : ∀ (X : Type) (l l' : List X) (m j : ℕ), l.take m = l'.take m → j < m →
      l[j]? = l'[j]? := by
    intro X l l' m j h hj
    have := congrArg (fun L : List X => L[j]?) h
    simpa [List.getElem?_take, hj] using this
  intro t
  induction t with
  | zero =>
    intro n c c' hl hvar hS
    simp only [zero_mul, add_zero] at hS
    simp only [Function.iterate_zero, id_eq, Option.map_some, hl, hvar]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext k
    exact hS k
  | succ t ih =>
    intro n c c' hl hvar hS
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    cases hcl : c.l with
    | none =>
      have hcl' : c'.l = none := hl ▸ hcl
      simp only [Option.bind_some]
      rw [hnone c hcl, hnone c' hcl']
    | some l =>
      have hcl' : c'.l = some l := hl ▸ hcl
      simp only [Option.bind_some]
      rw [hstep c l hcl, hstep c' l hcl', ← hvar]
      -- one-step locality (pnp-111) with the window n + t * b
      have hMul : (t + 1) * b = t * b + b := by ring
      have hS' := hS
      rw [hMul] at hS'
      have hcells : ∀ k, ∀ j, j ≤ b + (n + t * b) → (c.stk k)[j]? = (c'.stk k)[j]? := by
        intro k j hj
        apply fromTake _ _ _ (n + (t * b + b) + 1) j (hS' k) (by omega)
      obtain ⟨h1, h2, h3⟩ := MPP.Solutions.Pnp111.main K Γ Λ σ (M l) b (n + t * b) (hM l) c.var c.stk c'.stk
        hcells
      have hstk : ∀ k, ((TM2.stepAux (M l) c.var c.stk).stk k).take (n + t * b + 1) =
          ((TM2.stepAux (M l) c.var c'.stk).stk k).take (n + t * b + 1) := by
        intro k
        apply toTake
        intro i hi
        exact h3 k i (by omega)
      exact ih n _ _ h1 h2 hstk

end MPP.Solutions.Pnp112
