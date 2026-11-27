import Mathlib

namespace MPP.Solutions.Pnp331

def pstep (st : List Bool × List Bool × Option Bool) (b : Bool) : List Bool × List Bool × Option Bool :=
  match st.2.2 with
  | none => (st.1, st.2.1, some b)
  | some a =>
    if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
      else (st.1, st.2.1, none))
    else (if b then (st.1.headD false :: st.1, st.2.1, none)
      else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))

theorem pair_run (s t w : List Bool) (a b : Bool) (hs : 1 ≤ s.length)
    (hab : a && b = true → 2 ≤ s.length) :
    ∃ (s' : List Bool) (w' : List Bool),
      [a, b].foldl pstep (s, w, none) = (s', w', none) ∧
      [a, b].foldl pstep (s ++ t, w, none) = (s' ++ t, w', none) ∧
      (s'.length : ℤ) = (s.length : ℤ) + (if a && b then (-1 : ℤ) else if a then 0 else 1) := by
  rcases s with _ | ⟨x, s0⟩
  · simp at hs
  cases a <;> cases b
  · exact ⟨w.headD false :: x :: s0, w.drop 1, by simp [pstep], by simp [pstep], by simp⟩
  · exact ⟨x :: x :: s0, w, by simp [pstep], by simp [pstep], by simp⟩
  · exact ⟨x :: s0, w, by simp [pstep], by simp [pstep], by simp⟩
  · rcases s0 with _ | ⟨y, z⟩
    · simp at hab
    · exact ⟨(!(x && y)) :: z, w, by simp [pstep], by simp [pstep], by simp⟩

theorem run_suffix (T : List (Bool × Bool)) : ∀ (s t w : List Bool),
    (∀ j, j ≤ T.length → (1 : ℤ) ≤ (s.length : ℤ) +
      ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
    (T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep (s ++ t, w, none) =
      (((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep (s, w, none)).1 ++ t,
        ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep (s, w, none)).2.1,
        ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep (s, w, none)).2.2) ∧
    1 ≤ ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep (s, w, none)).1.length := by
  induction T with
  | nil =>
    intro s t w hc
    refine ⟨by simp, ?_⟩
    have h0 := hc 0 (by simp)
    simp at h0
    simp
    omega
  | cons r0 T ih =>
    intro s t w hc
    obtain ⟨a, b⟩ := r0
    have hs1 : 1 ≤ s.length := by
      have h0 := hc 0 (by simp)
      simp at h0
      omega
    have hab : a && b = true → 2 ≤ s.length := by
      intro hab
      obtain ⟨rfl, rfl⟩ : a = true ∧ b = true := by simpa using hab
      have h1 := hc 1 (by simp)
      simp [List.take_succ_cons] at h1
      omega
    obtain ⟨s1, w1, e1, e2, e3⟩ := pair_run s t w a b hs1 hab
    have hc' : ∀ j, j ≤ T.length → (1 : ℤ) ≤ (s1.length : ℤ) +
        ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
      intro j hj
      have h1 := hc (j + 1) (by simp only [List.length_cons]; omega)
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons] at h1
      linarith
    have IH := ih s1 t w1 hc'
    simp only [List.flatMap_cons, List.foldl_append]
    rw [e2, e1]
    exact ⟨IH.1, IH.2⟩

theorem main : ∀ (F : List Bool × List Bool × Option Bool → Bool → List Bool × List Bool × Option Bool),
      F = (fun st b => match st.2.2 with
        | none => (st.1, st.2.1, some b)
        | some a =>
          if a then (if b then ((!(st.1.headD false && (st.1.drop 1).headD false)) :: st.1.drop 2, st.2.1, none)
            else (st.1, st.2.1, none))
          else (if b then (st.1.headD false :: st.1, st.2.1, none)
            else (st.2.1.headD false :: st.1, st.2.1.drop 1, none))) →
      ∀ (T : List (Bool × Bool)),
        (∀ j, j ≤ T.length → 0 ≤ ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum) →
      ∀ (u : Bool) (t w : List Bool),
        ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F (u :: t, w, none)).1.headD false =
          ((T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl F ([u], w, none)).1.headD false := by
  intro F hF T hT u t w
  have hF' : F = pstep := hF
  subst hF'
  have hc : ∀ j, j ≤ T.length → (1 : ℤ) ≤ (([u].length : ℕ) : ℤ) +
      ((T.map fun r : Bool × Bool => if r.1 && r.2 then (-1 : ℤ) else if r.1 then 0 else 1).take j).sum := by
    intro j hj
    have h0 := hT j hj
    simp only [List.length_singleton, Nat.cast_one]
    linarith
  obtain ⟨h1, h2⟩ := run_suffix T [u] t w hc
  have e : u :: t = [u] ++ t := rfl
  rw [e, h1]
  generalize (T.flatMap fun r : Bool × Bool => [r.1, r.2]).foldl pstep ([u], w, none) = Y at h2 ⊢
  obtain ⟨X, Xw, Xp⟩ := Y
  simp only at h2 ⊢
  cases X with
  | nil => simp at h2
  | cons x xs => simp

end MPP.Solutions.Pnp331
