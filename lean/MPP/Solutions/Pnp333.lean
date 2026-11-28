import Mathlib

namespace MPP.Solutions.Pnp333

theorem pair_step_tail
    (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hF : F = fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none)))
    (H : Bool × Bool → ℤ)
    (hH : ∀ r : Bool × Bool, H r = if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)
    (r : Bool × Bool) (s t w : List Bool) (hs : 1 ≤ s.length) (hnand : r.1 && r.2 = true → 2 ≤ s.length) :
    ∃ s1 : List Bool,
      [r.1, r.2].foldl F (s, w, none) = (s1, w.drop ([r].countP fun q : Bool × Bool => !q.1 && !q.2), none) ∧
      (s1.length : ℤ) = s.length + H r ∧
      [r.1, r.2].foldl F (s ++ t, w, none) = (s1 ++ t, w.drop ([r].countP fun q : Bool × Bool => !q.1 && !q.2), none) := by
  obtain ⟨a, c⟩ := r
  subst hF
  rw [hH]
  rcases s with _ | ⟨x, s0⟩
  · simp at hs
  cases a <;> cases c
  · exact ⟨w.headD false :: x :: s0, by simp, by simp, by simp⟩
  · exact ⟨x :: x :: s0, by simp, by simp, by simp⟩
  · exact ⟨x :: s0, by simp, by simp, by simp⟩
  · rcases s0 with _ | ⟨y, s2⟩
    · simp at hnand
    · refine ⟨(!(x && y)) :: s2, by simp, by simp, by simp⟩

theorem core_tail
    (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool)
    (hF : F = fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none)))
    (H : Bool × Bool → ℤ)
    (hH : ∀ r : Bool × Bool, H r = if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) :
    ∀ (p : List (Bool × Bool)) (s t w : List Bool),
      (∀ j, j ≤ p.length → 1 ≤ (s.length : ℤ) + ((p.map H).take j).sum) →
      ∃ s' : List Bool,
        (p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (s, w, none) =
          (s', w.drop (p.countP fun q : Bool × Bool => !q.1 && !q.2), none) ∧
        (s'.length : ℤ) = s.length + (p.map H).sum ∧
        (p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (s ++ t, w, none) =
          (s' ++ t, w.drop (p.countP fun q : Bool × Bool => !q.1 && !q.2), none) := by
  intro p
  induction p with
  | nil =>
    intro s t w _
    exact ⟨s, by simp, by simp, by simp⟩
  | cons r rest ih =>
    intro s t w hp
    have h0 := hp 0 (by simp)
    have hs : 1 ≤ s.length := by simpa using h0
    have h1 := hp 1 (by simp)
    have e1 : ((r :: rest).map H).take 1 = [H r] := rfl
    rw [e1, List.sum_cons, List.sum_nil, add_zero] at h1
    have hnand : r.1 && r.2 = true → 2 ≤ s.length := by
      intro hr
      have hr1 : r.1 = true := (Bool.and_eq_true _ _).mp hr |>.1
      have hr2 : r.2 = true := by
        have := (Bool.and_eq_true _ _).mp hr |>.2
        simpa using this
      have hH' : H r = -1 := by
        rw [hH, hr1, hr2]
        simp
      rw [hH'] at h1
      omega
    obtain ⟨s1, h2, hl1, h2t⟩ := pair_step_tail F hF H hH r s t w hs hnand
    have hp' : ∀ j, j ≤ rest.length → 1 ≤ (s1.length : ℤ) + ((rest.map H).take j).sum := by
      intro j hj
      have h3 := hp (j + 1) (by simp; omega)
      have e2 : ((r :: rest).map H).take (j + 1) = H r :: (rest.map H).take j := rfl
      rw [e2, List.sum_cons] at h3
      rw [hl1]
      omega
    obtain ⟨s', h3, hl3, h3t⟩ := ih s1 t (w.drop ([r].countP fun q : Bool × Bool => !q.1 && !q.2)) hp'
    have hc : (r :: rest).countP (fun q : Bool × Bool => !q.1 && !q.2) =
        [r].countP (fun q : Bool × Bool => !q.1 && !q.2) + rest.countP (fun q : Bool × Bool => !q.1 && !q.2) := by
      simp [List.countP_cons]
      omega
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [List.flatMap_cons, List.foldl_append, h2, h3, hc, List.drop_drop]
    · rw [hl3, hl1]
      simp only [List.map_cons, List.sum_cons]
      ring
    · rw [List.flatMap_cons, List.foldl_append, h2t, h3t, hc, List.drop_drop]

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
    F = (fun st b => match st.2.2 with
      | none => (st.1, st.2.1, some b)
      | some a =>
        if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
          else (st.1, st.2.1, none))
        else (if b then (st.1.headD false :: st.1, st.2.1, none)
          else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
    ∀ (B1 B2 : List (Bool × Bool)),
      (B1.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
      (∀ j, j ≤ B1.length → 0 ≤ ((B1.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      ∀ (g : Bool) (w : List Bool),
        ((B1 ++ B2).flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F ([g], w, none) =
          (B2.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F
            ([((B1.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F ([g], w, none)).1.headD false],
             w.drop (B1.countP fun q : Bool × Bool => !q.1 && !q.2), none) := by
  intro F hF B1 B2 hsum hnn g w
  obtain ⟨s', h1, hl, -⟩ := core_tail F hF
    (fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1) (fun r => rfl)
    B1 [g] [] w (by
      intro j hj
      have h0 := hnn j hj
      simp only [List.length_singleton, Nat.cast_one]
      linarith)
  have h2 : (s'.length : ℤ) = 1 := by rw [hl, hsum]; simp
  have hl1 : s'.length = 1 := by exact_mod_cast h2
  obtain ⟨y, hy⟩ : ∃ y, s' = [y] := List.length_eq_one_iff.mp hl1
  rw [List.flatMap_append, List.foldl_append, h1, hy]
  simp

end MPP.Solutions.Pnp333
