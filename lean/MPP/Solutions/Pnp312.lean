import Mathlib

namespace MPP.Solutions.Pnp312

theorem main : ∀ (n t : ℕ) (g : (Fin 3 → Bool) → Bool) (x : List Bool) (a : ℕ → Bool),
    ((∀ i : Fin n, a i.val = x.getD i.val false) ∧
      ∀ s : Fin t, ∀ i : Fin n,
        a (n * (s.val + 1) + i.val) = g (fun j => a (n * s.val + (i.val + j.val) % n))) →
    ∀ s : ℕ, s ≤ t → ∀ i : Fin n,
      a (n * s + i.val) =
        (Nat.iterate (fun (r : ℕ → Bool) (k : ℕ) => g (fun j : Fin 3 => r ((k + j.val) % n)))
          s (fun k => x.getD k false)) i.val := by
  intro n t g x a hyp s
  obtain ⟨hinit, hstep⟩ := hyp
  induction s with
  | zero =>
    intro _ i
    simpa using hinit i
  | succ s ih =>
    intro hs i
    have hst : s < t := hs
    have hn : 0 < n := by have := i.isLt; omega
    have h1 : a (n * (s + 1) + i.val) = g (fun j : Fin 3 => a (n * s + (i.val + j.val) % n)) :=
      hstep ⟨s, hst⟩ i
    rw [h1, Function.iterate_succ_apply']
    congr 1
    funext j
    exact ih (le_of_lt hst) ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

end MPP.Solutions.Pnp312
