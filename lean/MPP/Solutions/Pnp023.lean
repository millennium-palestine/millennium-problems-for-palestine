import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp023

open Turing

section Aux

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- The most pushes onto stack `k` that one run of a statement can perform. -/
def pushes (k : K) : TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => (if k' = k then 1 else 0) + pushes k q
  | .peek _ _ q => pushes k q
  | .pop _ _ q => pushes k q
  | .load _ q => pushes k q
  | .branch _ q₁ q₂ => max (pushes k q₁) (pushes k q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (k : K) : ∀ (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)),
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes k q
  | .push k' f q, v, S => by
    have ih := stepAux_length k q v (Function.update S k' (f v :: S k'))
    by_cases h : k' = k
    · subst h
      simp [pushes, TM2.stepAux] at ih ⊢
      omega
    · simp [pushes, TM2.stepAux, Ne.symm h] at ih ⊢
      omega
  | .peek k' f q, v, S => by
    have ih := stepAux_length k q (f v (S k').head?) S
    simpa [pushes, TM2.stepAux] using ih
  | .pop k' f q, v, S => by
    have ih := stepAux_length k q (f v (S k').head?) (Function.update S k' (S k').tail)
    by_cases h : k' = k
    · subst h
      simp [pushes, TM2.stepAux] at ih ⊢
      omega
    · simp [pushes, TM2.stepAux, Ne.symm h] at ih ⊢
      omega
  | .load a q, v, S => by
    have ih := stepAux_length k q (a v) S
    simpa [pushes, TM2.stepAux] using ih
  | .branch f q₁ q₂, v, S => by
    cases hf : f v
    · simp only [TM2.stepAux, hf, cond_false, pushes]
      exact le_trans (stepAux_length k q₂ v S) (Nat.add_le_add_left (le_max_right _ _) _)
    · simp only [TM2.stepAux, hf, cond_true, pushes]
      exact le_trans (stepAux_length k q₁ v S) (Nat.add_le_add_left (le_max_left _ _) _)
  | .goto _, _, S => by
    simp [pushes, TM2.stepAux]
  | .halt, _, S => by
    simp [pushes, TM2.stepAux]

/-- Along a run of `n` machine steps, stack `k` grows by at most `C` per step. -/
theorem run_length (M : Λ → TM2.Stmt Γ Λ σ) (k : K) (C : ℕ) (hC : ∀ l, pushes k (M l) ≤ C) :
    ∀ (n : ℕ) (a c : TM2.Cfg Γ Λ σ),
      (fun o : Option (TM2.Cfg Γ Λ σ) => o.bind (TM2.step M))^[n] (some a) = some c →
        (c.stk k).length ≤ (a.stk k).length + C * n := by
  intro n
  induction n with
  | zero =>
    intro a c h
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    simp
  | succ n ih =>
    intro a c h
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := a
    cases l with
    | none =>
      simp [TM2.step, Function.iterate_fixed] at h
    | some l =>
      have hb : TM2.step M ⟨some l, v, S⟩ = some (TM2.stepAux (M l) v S) := rfl
      simp only [hb, Option.bind] at h
      have h2 := ih _ _ h
      have h3 := stepAux_length k (M l) v S
      have h4 := hC l
      have h5 : ((TM2.Cfg.mk (some l) v S : TM2.Cfg Γ Λ σ).stk k).length = (S k).length := rfl
      rw [Nat.mul_succ]
      omega

end Aux

/-- The initial configuration puts the input on the input stack only. -/
theorem initList_stk_length (tm : FinTM2) (k : tm.K) (l : List (tm.Γ tm.k₀)) :
    ((initList tm l).stk k).length ≤ l.length := by
  unfold initList
  dsimp only
  split
  · rename_i h
    subst h
    exact le_refl _
  · simp

section Main

theorem main : ∀ f : List Bool → List Bool,
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (id : List Bool → List Bool) f) →
    ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  intro f hf
  obtain ⟨T⟩ := hf
  haveI : Fintype T.tm.Λ := T.tm.ΛFin
  let C : ℕ := Finset.univ.sup (fun l => pushes T.tm.k₁ (T.tm.m l))
  have hC : ∀ l, pushes T.tm.k₁ (T.tm.m l) ≤ C := fun l =>
    Finset.le_sup (f := fun l => pushes T.tm.k₁ (T.tm.m l)) (Finset.mem_univ l)
  refine ⟨Polynomial.C C * T.time + Polynomial.X, fun x => ?_⟩
  have h := T.outputsFun x
  have hs := h.steps_le_m
  have he := h.evals_in_steps
  have h1 := run_length T.tm.m T.tm.k₁ C hC h.steps _ _ he
  have h2 : (haltList T.tm (List.map T.outputAlphabet.invFun (id (f x)))).stk T.tm.k₁ =
      List.map T.outputAlphabet.invFun (id (f x)) := by
    simp [haltList]
  have h3 := initList_stk_length T.tm T.tm.k₁ (List.map T.inputAlphabet.invFun (id x))
  rw [List.length_map] at h3
  have hid : (id x).length = x.length := rfl
  have h4 : C * h.steps ≤ C * T.time.eval x.length :=
    Nat.mul_le_mul_left C (by simpa using hs)
  rw [h2] at h1
  have hfx : (id (f x)).length = (f x).length := rfl
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    List.length_map] at h1 ⊢
  omega

end Main

end MPP.Solutions.Pnp023
