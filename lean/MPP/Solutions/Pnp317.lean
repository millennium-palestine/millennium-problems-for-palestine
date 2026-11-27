import Mathlib

namespace MPP.Solutions.Pnp317

theorem main : ∀ (n b t : ℕ) (G : Fin b → (Fin (3 * b) → Bool) → Bool) (x : List Bool) (a : ℕ → Bool),
    ((∀ k : Fin (n * b), a k.val = x.getD k.val false) ∧
      ∀ s : Fin t, ∀ i : Fin n, ∀ j : Fin b,
        a (n * b * (s.val + 1) + i.val * b + j.val) =
          G j (fun w : Fin (3 * b) => a (n * b * s.val + ((i.val + w.val / b) % n) * b + w.val % b))) →
    ∀ s : ℕ, s ≤ t → ∀ k : Fin (n * b),
      a (n * b * s + k.val) =
        (Nat.iterate (fun (r : ℕ → Bool) (m : ℕ) =>
          if h : m % b < b then
            G ⟨m % b, h⟩ (fun w : Fin (3 * b) => r (((m / b + w.val / b) % n) * b + w.val % b))
          else false) s (fun m => x.getD m false)) k.val := by
  intro n b t G x a hyp s
  obtain ⟨h0, hloc⟩ := hyp
  induction s with
  | zero =>
    intro _ k
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_zero, id_eq]
    exact h0 k
  | succ s ih =>
    intro hs k
    have ih' := ih (by omega)
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hb => by
      have := k.isLt
      simp [hb] at this)
    have hn : 0 < n := Nat.pos_of_ne_zero (fun hn => by
      have := k.isLt
      simp [hn] at this)
    have hkb : k.val % b < b := Nat.mod_lt _ hb
    have hki : k.val / b < n := by
      have := k.isLt
      rw [Nat.div_lt_iff_lt_mul hb]
      exact this
    have hdiv : k.val / b * b + k.val % b = k.val := Nat.div_add_mod' k.val b
    have hWin : ∀ w : Fin (3 * b), ((k.val / b + w.val / b) % n) * b + w.val % b < n * b := by
      intro w
      have hr : (k.val / b + w.val / b) % n < n := Nat.mod_lt _ hn
      have hq : w.val % b < b := Nat.mod_lt _ hb
      have hrb : ((k.val / b + w.val / b) % n + 1) * b ≤ n * b := Nat.mul_le_mul_right _ hr
      nlinarith
    have hL := hloc ⟨s, by omega⟩ ⟨k.val / b, hki⟩ ⟨k.val % b, hkb⟩
    have e : n * b * (s + 1) + k.val / b * b + k.val % b = n * b * (s + 1) + k.val := by
      rw [Nat.add_assoc, hdiv]
    simp only [] at hL
    rw [e] at hL
    rw [Function.iterate_succ_apply']
    show a (n * b * (s + 1) + k.val) = (if h : k.val % b < b then _ else false)
    rw [dif_pos hkb, hL]
    congr 1
    funext w
    have hw := ih' ⟨((k.val / b + w.val / b) % n) * b + w.val % b, hWin w⟩
    simpa only [Nat.add_assoc] using hw

end MPP.Solutions.Pnp317
