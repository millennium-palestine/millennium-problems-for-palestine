import Mathlib

namespace MPP.Solutions.Pnp169

/-- Two lists that agree on their first `N` entries agree on their first `M ≤ N` entries. -/
theorem take_agree {s s' : List Bool} {N M : ℕ} (h : s.take N = s'.take N) (hM : M ≤ N) :
    s.take M = s'.take M := by
  have h' := congrArg (List.take M) h
  simpa only [List.take_take, min_eq_left hM] using h'

/-- A window of a drop is determined by the window of the original list, when it lies inside. -/
theorem drop_take_agree {s s' : List Bool} {N k m : ℕ} (h : s.take N = s'.take N)
    (hk : k + m ≤ N) : (s.drop k).take m = (s'.drop k).take m := by
  rw [List.take_drop, List.take_drop, take_agree h hk]

/-- Dropping from an append, split at the length of the first list. -/
theorem drop_app (l1 l2 : List Bool) (n : ℕ) :
    (l1 ++ l2).drop n = l1.drop n ++ l2.drop (n - l1.length) := by
  induction l1 generalizing n with
  | nil => simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ m => simp [ih]

/-- The first two entries decide the head and the second entry of a stack. -/
theorem head_agree (s s' : List Bool) (h : s.take 2 = s'.take 2) :
    s.headD false = s'.headD false ∧ (s.drop 1).headD false = (s'.drop 1).headD false := by
  rcases s with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> rcases s' with _ | ⟨c, _ | ⟨d, u⟩⟩ <;> simp_all

/-- One pair `[a, b]` of the fan-out program, from stacks that agree on their top two entries,
has the same new top segment and the same drop count on both. -/
theorem pair_local (a b : Bool) (s s' w : List Bool) (h : s.take 2 = s'.take 2) :
    ∃ (t0 : List Bool) (k0 : ℕ) (w1 : List Bool), t0.length ≤ 1 ∧ k0 ≤ 2 ∧
      ([a, b].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
        = (t0 ++ s.drop k0, w1, none) ∧
      ([a, b].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s', w, none))
        = (t0 ++ s'.drop k0, w1, none) := by
  obtain ⟨h1, h2⟩ := head_agree s s' h
  cases a <;> cases b
  · exact ⟨[w.headD false], 0, w.drop 1, by simp, by norm_num, rfl, rfl⟩
  · exact ⟨[s.headD false], 0, w, by simp, by norm_num, rfl, by simp only [List.foldl, h1]; rfl⟩
  · exact ⟨[], 0, w, by simp, by norm_num, rfl, rfl⟩
  · exact ⟨[!(s.headD false && (s.drop 1).headD false)], 2, w, by simp, by norm_num, rfl,
      by simp only [List.foldl, h1, h2]; rfl⟩

theorem main : ∀ (ps : List (Bool × Bool)) (s s' w : List Bool), s.take (2 * ps.length) = s'.take (2 * ps.length) →
    ∃ (t : List Bool) (k : ℕ),
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1
      = t ++ s.drop k ∧
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s', w, none)).1
      = t ++ s'.drop k ∧
    t.length ≤ ps.length ∧ k ≤ 2 * ps.length := by
  intro ps
  induction ps with
  | nil => intro s s' w _; exact ⟨[], 0, by simp, by simp, by simp, by simp⟩
  | cons p ps ih =>
    intro s s' w h
    simp only [List.length_cons] at h
    have h2 : s.take 2 = s'.take 2 := take_agree h (by omega)
    obtain ⟨t0, k0, w1, ht0, hk0, hA, hB⟩ := pair_local p.1 p.2 s s' w h2
    have h3 : (t0 ++ s.drop k0).take (2 * ps.length) = (t0 ++ s'.drop k0).take (2 * ps.length) := by
      rw [List.take_append, List.take_append]
      congr 1
      exact drop_take_agree h (by omega)
    obtain ⟨t', k', h4, h5, h6, h7⟩ := ih (t0 ++ s.drop k0) (t0 ++ s'.drop k0) w1 h3
    refine ⟨t' ++ t0.drop k', k0 + (k' - t0.length), ?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.foldl_append]
      rw [hA, h4, drop_app, List.drop_drop]
      simp [List.append_assoc]
    · simp only [List.flatMap_cons, List.foldl_append]
      rw [hB, h5, drop_app, List.drop_drop]
      simp [List.append_assoc]
    · simp only [List.length_append, List.length_drop, List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

end MPP.Solutions.Pnp169
