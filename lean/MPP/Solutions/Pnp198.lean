import Mathlib

namespace MPP.Solutions.Pnp198

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

theorem main : ∀ q : List (Bool × Bool),
    (∀ j, j ≤ q.length → 0 ≤ ((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).sum = 0 →
    ∀ (t w : List Bool) (v : Bool), ∃ (g : Bool) (w' : List Bool),
      (q.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl (fun (st : List Bool × List Bool × Option Bool) (b : Bool) =>
        match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) (v :: t, w, none) = (g :: t, w', none) := by
  intro q hpos hsum t w v
  obtain ⟨r', w', h, hl⟩ := run_mid t q [v] w (by
    intro j hj
    show 1 ≤ (([v] : List Bool).length : ℤ) +
      (((q.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1)).take j).sum
    have h1 := hpos j hj
    simp only [List.length_singleton, Nat.cast_one]
    omega)
  have hs : (q.map stepZ).sum = 0 := hsum
  have hlen : r'.length = 1 := by
    simp only [List.length_singleton] at hl
    rw [hs] at hl
    omega
  obtain ⟨g, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨g, w', h⟩

end MPP.Solutions.Pnp198
