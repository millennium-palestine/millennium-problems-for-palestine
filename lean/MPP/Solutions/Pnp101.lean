import Mathlib
import MPP.Defs.PvsNP
import MPP.Solutions.Pnp023

namespace MPP.Solutions.Pnp101

open MPP.PvsNP Computability Turing MPP.Solutions.Pnp023

theorem main : ∀ L : Lang, InP L → ∃ T : TM2ComputableInPolyTime (id : List Bool → List Bool) encodeBool L,
    ∃ q : Polynomial ℕ, ∀ (x : List Bool) (n : ℕ) (c : TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ),
      n ≤ T.time.eval x.length →
      (fun o : Option (TM2.Cfg T.tm.Γ T.tm.Λ T.tm.σ) => o.bind (TM2.step T.tm.m))^[n]
        (some (initList T.tm (List.map T.inputAlphabet.invFun x))) = some c →
      ∀ k : T.tm.K, (c.stk k).length ≤ q.eval x.length := by
  intro L hL
  obtain ⟨T⟩ := hL
  haveI : Fintype T.tm.Λ := T.tm.ΛFin
  haveI : Fintype T.tm.K := T.tm.kFin
  let C : ℕ := ∑ k : T.tm.K, ∑ l : T.tm.Λ, pushes k (T.tm.m l)
  have hC : ∀ k : T.tm.K, ∀ l : T.tm.Λ, pushes k (T.tm.m l) ≤ C := by
    intro k l
    have h1 : pushes k (T.tm.m l) ≤ ∑ l' : T.tm.Λ, pushes k (T.tm.m l') :=
      Finset.single_le_sum (f := fun l' => pushes k (T.tm.m l')) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    have h2 : ∑ l' : T.tm.Λ, pushes k (T.tm.m l') ≤ C :=
      Finset.single_le_sum (f := fun k' => ∑ l' : T.tm.Λ, pushes k' (T.tm.m l'))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact le_trans h1 h2
  refine ⟨T, Polynomial.C C * T.time + Polynomial.X, ?_⟩
  intro x n c hn hrun k
  have h1 := run_length T.tm.m k C (hC k) n _ c hrun
  have h2 := initList_stk_length T.tm k (List.map T.inputAlphabet.invFun x)
  rw [List.length_map] at h2
  have h3 : C * n ≤ C * T.time.eval x.length := Nat.mul_le_mul_left C hn
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

end MPP.Solutions.Pnp101
