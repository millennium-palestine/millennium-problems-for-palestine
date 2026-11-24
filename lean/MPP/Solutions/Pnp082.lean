import Mathlib

namespace MPP.Solutions.Pnp082

theorem main : ∀ u v : List Bool, u.length = v.length →
    (u.map (fun b => !b) < v.map (fun b => !b) ↔ v < u) := by
  intro u
  induction u with
  | nil =>
    intro v hv
    cases v with
    | nil => simp
    | cons b v => simp at hv
  | cons a u ih =>
    intro v hv
    cases v with
    | nil => simp at hv
    | cons b v =>
      simp only [List.length_cons, Nat.succ.injEq] at hv
      have ih' := ih v hv
      cases a <;> cases b <;> simp [List.cons_lt_cons_iff, ih']

end MPP.Solutions.Pnp082
