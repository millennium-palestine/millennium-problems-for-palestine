import Mathlib
import MPP.Solutions.Pnp196

namespace MPP.Solutions.Pnp197

/-- One bit of the pnp-133 fold. -/
def stp (st : List Bool × List Bool × Option Bool) (b : Bool) : List Bool × List Bool × Option Bool :=
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))

/-- The height step of a pair. -/
def stepZ (r : Bool × Bool) : ℤ := if r.1 && r.2 then -1 else if r.1 then 0 else 1

theorem pair_step (X w r : List Bool) (p : Bool × Bool) (h : 1 ≤ (r.length : ℤ) + stepZ p) :
    ∃ r' w' : List Bool, stp (stp (r ++ X, w, none) p.1) p.2 = (r' ++ X, w', none) ∧
      (r'.length : ℤ) = r.length + stepZ p := by
  obtain ⟨a, b⟩ := p
  cases a <;> cases b
  · refine ⟨w.headD false :: r, w.drop 1, ?_, ?_⟩
    · simp [stp, List.cons_append]
    · simp [stepZ]
  · refine ⟨(r ++ X).headD false :: r, w, ?_, ?_⟩
    · simp [stp, List.cons_append]
    · simp [stepZ]
  · refine ⟨r, w, ?_, ?_⟩
    · simp [stp]
    · simp [stepZ]
  · match r, h with
    | x :: y :: r2, _ =>
      refine ⟨(!(x && y)) :: r2, w, ?_, ?_⟩
      · simp [stp, List.cons_append]
      · simp [stepZ]
    | [], h => simp [stepZ] at h
    | [_], h => simp [stepZ] at h

theorem run_mid (X : List Bool) : ∀ (mid : List (Bool × Bool)) (r w : List Bool),
    (∀ j, j ≤ mid.length → 1 ≤ (r.length : ℤ) + ((mid.map stepZ).take j).sum) →
    ∃ r' w' : List Bool, (mid.flatMap fun p : Bool × Bool => [p.1, p.2]).foldl stp (r ++ X, w, none) =
        (r' ++ X, w', none) ∧ (r'.length : ℤ) = r.length + (mid.map stepZ).sum := by
  intro mid
  induction mid with
  | nil =>
    intro r w _
    exact ⟨r, w, by simp, by simp⟩
  | cons p rest ih =>
    intro r w hyp
    obtain ⟨r1, w1, h1, hl1⟩ := pair_step X w r p (by simpa using hyp 1 (by simp))
    obtain ⟨r2, w2, h2, hl2⟩ := ih r1 w1 (by
      intro j hj
      have h3 := hyp (j + 1) (by simp only [List.length_cons]; omega)
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons] at h3
      omega)
    refine ⟨r2, w2, ?_, ?_⟩
    · rw [List.flatMap_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [h1]
      exact h2
    · simp only [List.map_cons, List.sum_cons]
      omega

theorem main : ∀ p : List (Bool × Bool),
    (p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    (∀ j, 0 < j → j < p.length →
      0 < ((p.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    ∀ (t w : List Bool) (v : Bool), ∃ g : Bool,
      ((p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none)).1 = g :: t := by
  intro p hsum hpos t w v
  show ∃ g : Bool, ((p.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl stp (v :: t, w, none)).1 = g :: t
  rcases Nat.lt_or_ge p.length 2 with hlt | hge
  · rcases p with _ | ⟨a, _ | ⟨c, rest⟩⟩
    · exact ⟨v, by simp⟩
    · obtain ⟨x, y⟩ := a
      cases x <;> cases y
      · simp at hsum
      · simp at hsum
      · exact ⟨v, by simp [stp]⟩
      · simp at hsum
    · simp at hlt
  · obtain ⟨a, c, mid, hp, ha, hc, hm, hmpos⟩ := MPP.Solutions.Pnp196.main p hge hsum
      (by
        intro j hj1 hj2
        have h5 := hpos j hj1 hj2
        simp only [List.map_take] at h5 ⊢
        exact h5)
    subst hp
    have ha' : stepZ a = 1 := ha
    have hc' : stepZ c = -1 := hc
    have hm' : (mid.map stepZ).sum = 0 := hm
    have hmpos' : ∀ j, j ≤ mid.length → 0 ≤ ((mid.map stepZ).take j).sum := hmpos
    obtain ⟨r1, w1, h1, hl1⟩ := pair_step (v :: t) w [] a (by simp [ha'])
    simp only [List.nil_append, List.length_nil, Nat.cast_zero, zero_add, ha'] at h1 hl1
    obtain ⟨r2, w2, h2, hl2⟩ := run_mid (v :: t) mid r1 w1 (by
      intro j hj
      have h4 := hmpos' j hj
      omega)
    rw [hm', add_zero, hl1] at hl2
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp (by omega : r2.length = 1)
    have hc2 : c = (true, true) := by
      obtain ⟨c1, c2⟩ := c
      cases c1 <;> cases c2 <;> simp [stepZ] at hc' ⊢
    subst hc2
    refine ⟨!(y && v), ?_⟩
    simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
    rw [List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h1, h2]
    simp [stp]

end MPP.Solutions.Pnp197
