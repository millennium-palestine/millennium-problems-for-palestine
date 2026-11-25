import Mathlib

namespace MPP.Solutions.Pnp154

/-- One pair `[a, b]` of the fan-out program, from a state with no pending bit,
leaves the stack as a new top segment `t0` on the old stack with `k0` top entries
removed. -/
theorem pair_step (a b : Bool) (s w : List Bool) :
    ∃ (t0 : List Bool) (k0 : ℕ) (w1 : List Bool), t0.length ≤ 1 ∧ k0 ≤ 2 ∧
      ([a, b].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
        = (t0 ++ s.drop k0, w1, none) := by
  cases a <;> cases b
  · exact ⟨[w.headD false], 0, w.drop 1, by simp, by norm_num, rfl⟩
  · exact ⟨[s.headD false], 0, w, by simp, by norm_num, rfl⟩
  · exact ⟨[], 0, w, by simp, by norm_num, rfl⟩
  · exact ⟨[!(s.headD false && (s.drop 1).headD false)], 2, w, by simp, by norm_num, rfl⟩

/-- Dropping from an append, split at the length of the first list. -/
theorem drop_app (l1 l2 : List Bool) (n : ℕ) :
    (l1 ++ l2).drop n = l1.drop n ++ l2.drop (n - l1.length) := by
  induction l1 generalizing n with
  | nil => simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ m => simp [ih]

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool), ∃ (t : List Bool) (k : ℕ),
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1
      = t ++ s.drop k ∧ t.length ≤ ps.length ∧ k ≤ 2 * ps.length := by
  intro ps
  induction ps with
  | nil => intro s w; exact ⟨[], 0, by simp⟩
  | cons p ps ih =>
    intro s w
    obtain ⟨t0, k0, w1, h0, h1, hst⟩ := pair_step p.1 p.2 s w
    obtain ⟨t', k', h2, h3, h4⟩ := ih (t0 ++ s.drop k0) w1
    refine ⟨t' ++ t0.drop k', k0 + (k' - t0.length), ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.foldl_append]
      rw [hst, h2, drop_app]
      simp [List.append_assoc]
    · simp only [List.length_append, List.length_drop, List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

end MPP.Solutions.Pnp154
