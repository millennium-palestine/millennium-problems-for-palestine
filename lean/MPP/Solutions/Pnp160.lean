import Mathlib

namespace MPP.Solutions.Pnp160

/-- One pair `[a, b]` from a state with no pending bit: the new top segment `t0`
(at most one entry) sits on the old stack with `k0` entries removed, where `k0`
is two for a NAND pair `(true, true)` and zero otherwise. -/
theorem pair_exact (a b : Bool) (s w : List Bool) :
    ∃ (t0 : List Bool) (w1 : List Bool), t0.length ≤ 1 ∧
      ([a, b].foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none))
        = (t0 ++ s.drop (if a && b then 2 else 0), w1, none) := by
  cases a <;> cases b
  · exact ⟨[w.headD false], w.drop 1, by simp, rfl⟩
  · exact ⟨[s.headD false], w, by simp, rfl⟩
  · exact ⟨[], w, by simp, rfl⟩
  · exact ⟨[!(s.headD false && (s.drop 1).headD false)], w, by simp, rfl⟩

/-- Dropping from an append, split at the length of the first list. -/
theorem drop_app (l1 l2 : List Bool) (n : ℕ) :
    (l1 ++ l2).drop n = l1.drop n ++ l2.drop (n - l1.length) := by
  induction l1 generalizing n with
  | nil => simp
  | cons x l ih =>
    cases n with
    | zero => simp
    | succ m => simp [ih]

/-- A short top segment `t0` (at most one entry) absorbed by a drop of `K` entries from
`t0 ++ s.drop k` leaves a segment of length at most `t0.length` over `s.drop (k + K)`. -/
theorem absorb (t0 : List Bool) (ht : t0.length ≤ 1) (s : List Bool) (k K : ℕ) :
    ∃ X : List Bool, X.length ≤ t0.length ∧ (t0 ++ s.drop k).drop K = X ++ s.drop (k + K) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    exact ⟨t0, le_rfl, by simp⟩
  · have hle : t0.length ≤ K := by omega
    refine ⟨(s.drop (k + K - t0.length)).take t0.length, List.length_take_le _ _, ?_⟩
    rw [drop_app, List.drop_eq_nil_of_le hle, List.nil_append, List.drop_drop]
    have h1 : k + (K - t0.length) = k + K - t0.length := by omega
    rw [h1]
    have h2 : s.drop (k + K - t0.length) = (s.drop (k + K - t0.length)).take t0.length
        ++ (s.drop (k + K - t0.length)).drop t0.length := (List.take_append_drop _ _).symm
    have h3 : (s.drop (k + K - t0.length)).drop t0.length = s.drop (k + K) := by
      rw [List.drop_drop]
      congr 1
      omega
    conv_lhs => rw [h2, h3]

theorem main : ∀ (ps : List (Bool × Bool)) (s w : List Bool), ∃ t : List Bool,
    ((ps.flatMap fun q => [q.1, q.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
      match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (s, w, none)).1
      = t ++ s.drop (2 * ps.countP (fun q => q.1 && q.2)) ∧ t.length ≤ ps.length := by
  intro ps
  induction ps with
  | nil => intro s w; exact ⟨[], by simp, by simp⟩
  | cons p ps ih =>
    intro s w
    obtain ⟨t0, w1, h0, hst⟩ := pair_exact p.1 p.2 s w
    obtain ⟨t', h2, h3⟩ := ih (t0 ++ s.drop (if p.1 && p.2 then 2 else 0)) w1
    obtain ⟨X, hX, hXeq⟩ := absorb t0 h0 s (if p.1 && p.2 then 2 else 0)
      (2 * ps.countP (fun q => q.1 && q.2))
    refine ⟨t' ++ X, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.foldl_append]
      rw [hst, h2, hXeq, List.countP_cons]
      have hk : 2 * (ps.countP (fun q => q.1 && q.2) + if (fun q : Bool × Bool => q.1 && q.2) p then 1 else 0)
          = (if p.1 && p.2 then 2 else 0) + 2 * ps.countP (fun q => q.1 && q.2) := by
        rcases p with ⟨a, b⟩
        cases a <;> cases b <;> simp <;> omega
      rw [hk, ← List.append_assoc]
    · simp only [List.length_cons, List.length_append]
      omega

end MPP.Solutions.Pnp160
