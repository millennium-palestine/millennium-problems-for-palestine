import Mathlib

namespace MPP.Solutions.Pnp275

theorem pad_pair
    (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hF : F = fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none)))
    (st : List Bool × List Bool × Option Bool) (hs : st.2.2 = none) :
    ([true, false].foldl F st) = st := by
  obtain ⟨a, b, p⟩ := st
  simp only at hs
  subst hs hF
  rfl

theorem pad_run
    (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hF : F = fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none)))
    (k : ℕ) (st : List Bool × List Bool × Option Bool) (hs : st.2.2 = none) :
    ((List.replicate k [true, false]).flatten.foldl F st) = st := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, pad_pair F hF st hs]
    exact ih

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
    F = (fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (bits w : List Bool) (k : ℕ), (bits.foldl F ([], w, none)).2.2 = none →
      (bits ++ (List.replicate k [true, false]).flatten).foldl F ([], w, none) = bits.foldl F ([], w, none) := by
  intro F hF bits w k h
  rw [List.foldl_append, pad_run F hF k _ h]

end MPP.Solutions.Pnp275
