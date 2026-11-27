import Mathlib
import MPP.Solutions.Pnp312
import MPP.Solutions.Pnp313

namespace MPP.Solutions.Pnp314

theorem main : ∀ (n t : ℕ) (g : (Fin 3 → Bool) → Bool) (x : List Bool), 0 < n →
    ((∃ a : ℕ → Bool, ((∀ i : Fin n, a i.val = x.getD i.val false) ∧
        ∀ s : Fin t, ∀ i : Fin n,
          a (n * (s.val + 1) + i.val) = g (fun j => a (n * s.val + (i.val + j.val) % n))) ∧
        a (n * t) = true) ↔
      (Nat.iterate (fun (r : ℕ → Bool) (k : ℕ) => g (fun j : Fin 3 => r ((k + j.val) % n)))
        t (fun k => x.getD k false)) 0 = true) := by
  intro n t g x hn
  constructor
  · rintro ⟨a, ⟨hinit, hstep⟩, hout⟩
    have h := MPP.Solutions.Pnp312.main n t g x a ⟨hinit, hstep⟩ t le_rfl ⟨0, hn⟩
    rw [show n * t + (⟨0, hn⟩ : Fin n).val = n * t from rfl, hout] at h
    exact h.symm
  · intro hout
    obtain ⟨a, hA⟩ := MPP.Solutions.Pnp313.main n t g x
    refine ⟨a, hA, ?_⟩
    have h := MPP.Solutions.Pnp312.main n t g x a hA t le_rfl ⟨0, hn⟩
    rw [show n * t + (⟨0, hn⟩ : Fin n).val = n * t from rfl] at h
    rw [h]
    exact hout

end MPP.Solutions.Pnp314
