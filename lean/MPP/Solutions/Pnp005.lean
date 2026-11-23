import Mathlib
import MPP.Defs.PvsNP

namespace MPP.Solutions.Pnp005

open MPP.PvsNP

theorem pair_nil_eq (w : List Bool) : pair [] w = false :: true :: w := by
  simp [pair]

theorem pair_cons_eq (b : Bool) (x w : List Bool) :
    pair (b :: x) w = b :: b :: pair x w := by
  simp [pair]

theorem main :
    ∀ x w x' w' : List Bool, pair x w = pair x' w' → x = x' ∧ w = w' := by
  intro x
  induction x with
  | nil =>
    intro w x' w' h
    cases x' with
    | nil =>
      rw [pair_nil_eq, pair_nil_eq] at h
      exact ⟨rfl, (List.cons.inj (List.cons.inj h).2).2⟩
    | cons c x'' =>
      rw [pair_nil_eq, pair_cons_eq] at h
      cases c <;> simp at h
  | cons b x ih =>
    intro w x' w' h
    cases x' with
    | nil =>
      rw [pair_cons_eq, pair_nil_eq] at h
      cases b <;> simp at h
    | cons c x'' =>
      rw [pair_cons_eq, pair_cons_eq] at h
      obtain ⟨hbc, h2⟩ := List.cons.inj h
      obtain ⟨-, h3⟩ := List.cons.inj h2
      obtain ⟨hx, hw⟩ := ih w x'' w' h3
      subst hx
      subst hbc
      exact ⟨rfl, hw⟩

end MPP.Solutions.Pnp005
