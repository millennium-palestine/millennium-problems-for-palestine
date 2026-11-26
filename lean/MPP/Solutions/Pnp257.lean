import Mathlib

namespace MPP.Solutions.Pnp257

-- The fold reads its input two bits at a time: it stores a pending bit at the first bit of a pair and
-- executes the instruction at the second. Every step flips the pending bit between none and some.
theorem pending_iff (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (h1 : ∀ s b, s.2.2 = none → (F s b).2.2 ≠ none)
    (h2 : ∀ s b, s.2.2 ≠ none → (F s b).2.2 = none) :
    ∀ (g : List Bool) (s : List Bool × List Bool × Option Bool),
      (g.foldl F s).2.2 = none ↔ (s.2.2 = none ↔ g.length % 2 = 0) := by
  intro g
  induction g with
  | nil => intro s; simp
  | cons x xs ih =>
    intro s
    have key : (xs.length + 1) % 2 = 0 ↔ ¬ (xs.length % 2 = 0) := by omega
    rw [List.foldl_cons, ih]
    by_cases hs : s.2.2 = none
    · have hne := h1 s x hs
      simp [hs, hne, key]
    · simp [hs, h2 s x hs, key]

-- A padding pair (true, false) acts as the identity on a state with no pending bit.
theorem pad_id (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hpair : ∀ t : List Bool × List Bool × Option Bool, t.2.2 = none → [true, false].foldl F t = t) :
    ∀ (k : ℕ) (t : List Bool × List Bool × Option Bool), t.2.2 = none →
      ((List.replicate k [true, false]).flatten).foldl F t = t := by
  intro k
  induction k with
  | zero => intro t _; rfl
  | succ k ih =>
    intro t ht
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, hpair t ht]
    exact ih t ht

theorem pad_main (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (h1 : ∀ s b, s.2.2 = none → (F s b).2.2 ≠ none)
    (h2 : ∀ s b, s.2.2 ≠ none → (F s b).2.2 = none)
    (hpair : ∀ t : List Bool × List Bool × Option Bool, t.2.2 = none → [true, false].foldl F t = t) :
    ∀ (g : List Bool) (k : ℕ) (w : List Bool), g.length % 2 = 0 →
      (g ++ (List.replicate k [true, false]).flatten).foldl F ([], w, none)
        = g.foldl F ([], w, none) := by
  intro g k w hg
  rw [List.foldl_append]
  exact pad_id F hpair k _ ((pending_iff F h1 h2 g ([], w, none)).mpr (by simp [hg]))

theorem main : ∀ (g : List Bool) (k : ℕ) (w : List Bool), g.length % 2 = 0 →
    (g ++ (List.replicate k [true, false]).flatten).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([], w, none)
    = g.foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) ([], w, none) := by
  refine pad_main _ ?_ ?_ ?_
  · rintro ⟨st, v, p⟩ b h
    cases p with
    | none => simp
    | some a => simp at h
  · rintro ⟨st, v, p⟩ b h
    cases p with
    | none => exact absurd rfl h
    | some a => cases a <;> cases b <;> rfl
  · rintro ⟨st, v, p⟩ h
    cases p with
    | none => rfl
    | some a => simp at h

end MPP.Solutions.Pnp257
