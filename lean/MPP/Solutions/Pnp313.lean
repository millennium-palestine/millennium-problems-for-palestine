import Mathlib

namespace MPP.Solutions.Pnp313

theorem main : ∀ (n t : ℕ) (g : (Fin 3 → Bool) → Bool) (x : List Bool), ∃ a : ℕ → Bool,
    (∀ i : Fin n, a i.val = x.getD i.val false) ∧
      ∀ s : Fin t, ∀ i : Fin n,
        a (n * (s.val + 1) + i.val) = g (fun j => a (n * s.val + (i.val + j.val) % n)) := by
  intro n t g x
  have hdiv : ∀ q r : ℕ, r < n → (n * q + r) / n = q ∧ (n * q + r) % n = r := by
    intro q r hr
    have hn : 0 < n := by omega
    exact ⟨by rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero],
      by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩
  refine ⟨fun k => Nat.iterate (fun (r : ℕ → Bool) (k : ℕ) => g (fun j : Fin 3 => r ((k + j.val) % n)))
    (k / n) (fun k => x.getD k false) (k % n), ?_, ?_⟩
  · intro i
    have hi := i.isLt
    have h0 : i.val / n = 0 := Nat.div_eq_of_lt hi
    have h1 : i.val % n = i.val := Nat.mod_eq_of_lt hi
    simp only [h0, h1, Function.iterate_zero, id_eq]
  · intro s i
    have hi := i.isLt
    have hn : 0 < n := by omega
    dsimp only
    rw [(hdiv (s.val + 1) i.val hi).1, (hdiv (s.val + 1) i.val hi).2, Function.iterate_succ_apply']
    congr 1
    funext j
    rw [(hdiv s.val ((i.val + j.val) % n) (Nat.mod_lt _ hn)).1,
      (hdiv s.val ((i.val + j.val) % n) (Nat.mod_lt _ hn)).2]

end MPP.Solutions.Pnp313
